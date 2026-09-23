import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5HyperbolicGaussianTailCore
import GaloisForLFunctions.RHTower.ThetaCuspAtomLikelihoodCrossDomination
import GaloisForLFunctions.RHTower.CothInfra

open Set

namespace RHTower

noncomputable section

/-- Euler-scale derivative of the exact first-atom reflection coefficient. -/
def c5SingleAtomScaleLambdaJetOne (A : ℝ) : ℝ :=
  -6 * A * (A + 3 / 2) / (A - 3 / 2) ^ (3 : ℕ)

theorem c5SingleAtomScaleLambdaJetOne_eq
    {A : ℝ} (hA : 3 / 2 < A) :
    c5SingleAtomScaleLambdaJetOne A =
      -2 * (A + 3 / 2) / (A - 3 / 2) *
        thetaCuspSingleAtomReflectionLambda A := by
  unfold c5SingleAtomScaleLambdaJetOne thetaCuspSingleAtomReflectionLambda
  field_simp [ne_of_gt (sub_pos.mpr hA)]
  ring

theorem c5SingleAtomScaleLambdaJetOne_neg
    {A : ℝ} (hA : 3 < A) :
    c5SingleAtomScaleLambdaJetOne A < 0 := by
  unfold c5SingleAtomScaleLambdaJetOne
  have hb : 0 < A - 3 / 2 := by linarith
  have hnum : -6 * A * (A + 3 / 2) < 0 := by
    have hprod : 0 < 6 * A * (A + 3 / 2) := by positivity
    nlinarith
  exact div_neg_of_neg_of_pos hnum (pow_pos hb 3)

theorem c5SingleAtomScaleLambdaJetOne_lt_neg_two_mul
    {A : ℝ} (hA : 3 < A) :
    c5SingleAtomScaleLambdaJetOne A <
      -2 * thetaCuspSingleAtomReflectionLambda A := by
  rw [c5SingleAtomScaleLambdaJetOne_eq (by linarith)]
  have hl := thetaCuspSingleAtomReflectionLambda_pos hA
  have hratio : 1 < (A + 3 / 2) / (A - 3 / 2) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hm := mul_lt_mul_of_pos_right hratio hl
  calc
    -2 * (A + 3 / 2) / (A - 3 / 2) *
        thetaCuspSingleAtomReflectionLambda A =
      (-2) * (((A + 3 / 2) / (A - 3 / 2)) *
        thetaCuspSingleAtomReflectionLambda A) := by ring
    _ < (-2) * (1 * thetaCuspSingleAtomReflectionLambda A) :=
      mul_lt_mul_of_neg_left hm (by norm_num)
    _ = -2 * thetaCuspSingleAtomReflectionLambda A := by ring

theorem neg_six_mul_lt_c5SingleAtomScaleLambdaJetOne
    {A : ℝ} (hA : 3 < A) :
    -6 * thetaCuspSingleAtomReflectionLambda A <
      c5SingleAtomScaleLambdaJetOne A := by
  rw [c5SingleAtomScaleLambdaJetOne_eq (by linarith)]
  have hl := thetaCuspSingleAtomReflectionLambda_pos hA
  have hratio : (A + 3 / 2) / (A - 3 / 2) < 3 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have hm := mul_lt_mul_of_pos_right hratio hl
  calc
    -6 * thetaCuspSingleAtomReflectionLambda A =
      (-2) * (3 * thetaCuspSingleAtomReflectionLambda A) := by ring
    _ < (-2) * (((A + 3 / 2) / (A - 3 / 2)) *
        thetaCuspSingleAtomReflectionLambda A) :=
      mul_lt_mul_of_neg_left hm (by norm_num)
    _ = -2 * (A + 3 / 2) / (A - 3 / 2) *
        thetaCuspSingleAtomReflectionLambda A := by ring

theorem hasDerivAt_thetaCuspSingleAtomReflectionLambda
    {A : ℝ} (hA : 3 / 2 < A) :
    HasDerivAt thetaCuspSingleAtomReflectionLambda
      (c5SingleAtomScaleLambdaJetOne A / (2 * A)) A := by
  have hnum := (hasDerivAt_id A).const_mul 3
  have hden := ((hasDerivAt_id A).sub_const (3 / 2)).pow 2
  have hden0 : (A - 3 / 2) ^ (2 : ℕ) ≠ 0 := by positivity
  have hraw := hnum.fun_div hden hden0
  unfold thetaCuspSingleAtomReflectionLambda
  change HasDerivAt (fun x : ℝ => 3 * x / (x - 3 / 2) ^ (2 : ℕ))
    (c5SingleAtomScaleLambdaJetOne A / (2 * A)) A
  apply hraw.congr_deriv
  dsimp
  unfold c5SingleAtomScaleLambdaJetOne
  field_simp [ne_of_gt (by linarith : 0 < A), ne_of_gt (sub_pos.mpr hA)]
  ring

theorem hasDerivAt_thetaCuspSingleAtomReflectionLambda_scale
    {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt
      (fun x => thetaCuspSingleAtomReflectionLambda
        (thetaCuspSingleAtomReflectionScale 1 x))
      (c5SingleAtomScaleLambdaJetOne
        (thetaCuspSingleAtomReflectionScale 1 u)) u := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hu
  have houter := hasDerivAt_thetaCuspSingleAtomReflectionLambda
    (A := A) (by linarith)
  have hscale := hasDerivAt_thetaCuspSingleAtomReflectionScale_one u
  have hcomp := houter.comp u hscale
  have hcomp' : HasDerivAt
      (fun x => thetaCuspSingleAtomReflectionLambda
        (thetaCuspSingleAtomReflectionScale 1 x))
      ((c5SingleAtomScaleLambdaJetOne A / (2 * A)) *
        (2 * thetaCuspSingleAtomReflectionScale 1 u)) u :=
    hcomp.congr_of_eventuallyEq (by filter_upwards [] with x; rfl)
  have hvalue :
      (c5SingleAtomScaleLambdaJetOne A / (2 * A)) *
          (2 * thetaCuspSingleAtomReflectionScale 1 u) =
        c5SingleAtomScaleLambdaJetOne A := by
    have hA0 : 0 < A := by linarith
    rw [show thetaCuspSingleAtomReflectionScale 1 u = A by rfl]
    exact div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hA0.ne')
  rw [hvalue] at hcomp'
  simpa only [A] using hcomp'

/-- Exact centre derivative of first-atom reflected action under `A' = 2A`. -/
def c5SingleAtomScaleActionJetOne (A z : ℝ) : ℝ :=
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  4 * A * z + d * z / r

/-- Exact centre derivative of the first displacement jet. -/
def c5SingleAtomScaleMixedJetOne (A z z' : ℝ) : ℝ :=
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  (4 * A + d / r ^ (2 : ℕ)) * z'

/-- Exact centre derivative of the second displacement jet. -/
def c5SingleAtomScaleMixedJetTwo (A z : ℝ) : ℝ :=
  let l := thetaCuspSingleAtomReflectionLambda A
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  4 * (2 * l * d / r ^ (3 : ℕ) * z * (z + 2) +
    (4 * A + d / r ^ (2 : ℕ)) * (z + 1))

theorem hasDerivAt_thetaCuspSingleAtomReflectedAction_scale
    {u t : ℝ} (hu : 0 ≤ u)
    (hr : thetaCuspSingleAtomReflectionFactor
      (thetaCuspSingleAtomReflectionScale 1 u)
      (thetaCuspSingleAtomReflectionDefect t) ≠ 0) :
    HasDerivAt
      (fun x => thetaCuspSingleAtomReflectedAction
        (thetaCuspSingleAtomReflectionScale 1 x) t)
      (c5SingleAtomScaleActionJetOne
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t)) u := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let lfun := fun x => thetaCuspSingleAtomReflectionLambda
    (thetaCuspSingleAtomReflectionScale 1 x)
  let rfun := fun x => 1 - lfun x * z
  have hscale := hasDerivAt_thetaCuspSingleAtomReflectionScale_one u
  have hl := hasDerivAt_thetaCuspSingleAtomReflectionLambda_scale hu
  have hrfun : HasDerivAt rfun
      (-c5SingleAtomScaleLambdaJetOne A * z) u := by
    have hraw := (hasDerivAt_const u 1).sub (hl.mul_const z)
    have hcongr : rfun =ᶠ[nhds u]
        (fun x => 1 -
          thetaCuspSingleAtomReflectionLambda
            (thetaCuspSingleAtomReflectionScale 1 x) * z) := by
      filter_upwards [] with x
      rfl
    have hderiv := hraw.congr_of_eventuallyEq hcongr
    apply hderiv.congr_deriv
    ring
  have hmain := (hscale.const_mul (2 * z)).sub (hrfun.log (by
    dsimp only [rfun, lfun, A, z]
    simpa only [thetaCuspSingleAtomReflectionFactor] using hr))
  have hfun :
      (fun x => thetaCuspSingleAtomReflectedAction
        (thetaCuspSingleAtomReflectionScale 1 x) t) =
      (fun x => 2 * z * thetaCuspSingleAtomReflectionScale 1 x) -
        fun x => Real.log (rfun x) := by
    funext x
    dsimp only [rfun, lfun, z]
    unfold thetaCuspSingleAtomReflectedAction
      thetaCuspSingleAtomReflectionFactor
    congr 1
    ring
  rw [hfun]
  apply hmain.congr_deriv
  have hrfun_eq : rfun u =
      thetaCuspSingleAtomReflectionFactor A z := by rfl
  rw [hrfun_eq]
  unfold c5SingleAtomScaleActionJetOne
  dsimp only [A, z]
  field_simp [hr]
  ring

theorem hasDerivAt_thetaCuspSingleAtomReflectionSlope_scale
    {u z : ℝ} (hu : 0 ≤ u)
    (hr : thetaCuspSingleAtomReflectionFactor
      (thetaCuspSingleAtomReflectionScale 1 u) z ≠ 0) :
    HasDerivAt
      (fun x => thetaCuspSingleAtomReflectionSlope
        (thetaCuspSingleAtomReflectionScale 1 x) z)
      (4 * thetaCuspSingleAtomReflectionScale 1 u +
        c5SingleAtomScaleLambdaJetOne
          (thetaCuspSingleAtomReflectionScale 1 u) /
            thetaCuspSingleAtomReflectionFactor
              (thetaCuspSingleAtomReflectionScale 1 u) z ^ (2 : ℕ)) u := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let lfun := fun x => thetaCuspSingleAtomReflectionLambda
    (thetaCuspSingleAtomReflectionScale 1 x)
  let rfun := fun x => 1 - lfun x * z
  have hscale := hasDerivAt_thetaCuspSingleAtomReflectionScale_one u
  have hl := hasDerivAt_thetaCuspSingleAtomReflectionLambda_scale hu
  have hrfun : HasDerivAt rfun
      (-c5SingleAtomScaleLambdaJetOne A * z) u := by
    have hraw := (hasDerivAt_const u 1).sub (hl.mul_const z)
    have hcongr : rfun =ᶠ[nhds u]
        (fun x => 1 -
          thetaCuspSingleAtomReflectionLambda
            (thetaCuspSingleAtomReflectionScale 1 x) * z) := by
      filter_upwards [] with x
      rfl
    have hderiv := hraw.congr_of_eventuallyEq hcongr
    apply hderiv.congr_deriv
    ring
  have hrfun0 : rfun u ≠ 0 := by
    dsimp only [rfun, lfun, A]
    simpa only [thetaCuspSingleAtomReflectionFactor] using hr
  have hquot := hl.fun_div hrfun hrfun0
  have hmain := (hscale.const_mul 2).add hquot
  have hfun :
      (fun x => thetaCuspSingleAtomReflectionSlope
        (thetaCuspSingleAtomReflectionScale 1 x) z) =
      (fun x => 2 * thetaCuspSingleAtomReflectionScale 1 x) +
        fun x => lfun x / rfun x := by
    funext x
    unfold thetaCuspSingleAtomReflectionSlope
      thetaCuspSingleAtomReflectionFactor
    rfl
  rw [hfun]
  apply hmain.congr_deriv
  have hrfun_eq : rfun u =
      thetaCuspSingleAtomReflectionFactor A z := by rfl
  rw [hrfun_eq]
  dsimp only [A]
  unfold thetaCuspSingleAtomReflectionFactor at hr ⊢
  field_simp [hr]
  ring

theorem hasDerivAt_thetaCuspSingleAtomReflectedActionJetOne_scale
    {u z z' : ℝ} (hu : 0 ≤ u)
    (hr : thetaCuspSingleAtomReflectionFactor
      (thetaCuspSingleAtomReflectionScale 1 u) z ≠ 0) :
    HasDerivAt
      (fun x => thetaCuspSingleAtomReflectedActionJetOne
        (thetaCuspSingleAtomReflectionScale 1 x) z z')
      (c5SingleAtomScaleMixedJetOne
        (thetaCuspSingleAtomReflectionScale 1 u) z z') u := by
  have hslope := hasDerivAt_thetaCuspSingleAtomReflectionSlope_scale hu hr
  have hraw := hslope.mul_const z'
  unfold thetaCuspSingleAtomReflectedActionJetOne
    c5SingleAtomScaleMixedJetOne
  exact hraw

theorem hasDerivAt_thetaCuspSingleAtomReflectionCurvature_scale
    {u z : ℝ} (hu : 0 ≤ u)
    (hr : thetaCuspSingleAtomReflectionFactor
      (thetaCuspSingleAtomReflectionScale 1 u) z ≠ 0) :
    HasDerivAt
      (fun x =>
        thetaCuspSingleAtomReflectionLambda
            (thetaCuspSingleAtomReflectionScale 1 x) ^ (2 : ℕ) /
          thetaCuspSingleAtomReflectionFactor
            (thetaCuspSingleAtomReflectionScale 1 x) z ^ (2 : ℕ))
      (2 * thetaCuspSingleAtomReflectionLambda
          (thetaCuspSingleAtomReflectionScale 1 u) *
        c5SingleAtomScaleLambdaJetOne
          (thetaCuspSingleAtomReflectionScale 1 u) /
        thetaCuspSingleAtomReflectionFactor
          (thetaCuspSingleAtomReflectionScale 1 u) z ^ (3 : ℕ)) u := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let lfun := fun x => thetaCuspSingleAtomReflectionLambda
    (thetaCuspSingleAtomReflectionScale 1 x)
  let rfun := fun x => 1 - lfun x * z
  have hl := hasDerivAt_thetaCuspSingleAtomReflectionLambda_scale hu
  have hrfun : HasDerivAt rfun
      (-c5SingleAtomScaleLambdaJetOne A * z) u := by
    have hraw := (hasDerivAt_const u 1).sub (hl.mul_const z)
    have hcongr : rfun =ᶠ[nhds u]
        (fun x => 1 -
          thetaCuspSingleAtomReflectionLambda
            (thetaCuspSingleAtomReflectionScale 1 x) * z) := by
      filter_upwards [] with x
      rfl
    have hderiv := hraw.congr_of_eventuallyEq hcongr
    apply hderiv.congr_deriv
    ring
  have hrfun0 : rfun u ≠ 0 := by
    dsimp only [rfun, lfun, A]
    simpa only [thetaCuspSingleAtomReflectionFactor] using hr
  have hquot := hl.fun_div hrfun hrfun0
  have hsquare := hquot.pow 2
  have hfun :
      (fun x =>
        thetaCuspSingleAtomReflectionLambda
            (thetaCuspSingleAtomReflectionScale 1 x) ^ (2 : ℕ) /
          thetaCuspSingleAtomReflectionFactor
            (thetaCuspSingleAtomReflectionScale 1 x) z ^ (2 : ℕ)) =
      fun x => (lfun x / rfun x) ^ (2 : ℕ) := by
    funext x
    dsimp only [lfun, rfun]
    unfold thetaCuspSingleAtomReflectionFactor
    rw [div_pow]
  rw [hfun]
  apply hsquare.congr_deriv
  have hrfun_eq : rfun u =
      thetaCuspSingleAtomReflectionFactor A z := by rfl
  rw [hrfun_eq]
  dsimp only [A]
  have hr' :
      1 - thetaCuspSingleAtomReflectionLambda
        (thetaCuspSingleAtomReflectionScale 1 u) * z ≠ 0 := by
    simpa only [thetaCuspSingleAtomReflectionFactor] using hr
  unfold thetaCuspSingleAtomReflectionFactor
  norm_num
  field_simp [hr']
  ring

theorem hasDerivAt_thetaCuspSingleAtomReflectedActionJetTwo_scale
    {u z : ℝ} (hu : 0 ≤ u)
    (hr : thetaCuspSingleAtomReflectionFactor
      (thetaCuspSingleAtomReflectionScale 1 u) z ≠ 0) :
    HasDerivAt
      (fun x => thetaCuspSingleAtomReflectedActionJetTwo
        (thetaCuspSingleAtomReflectionScale 1 x) z)
      (c5SingleAtomScaleMixedJetTwo
        (thetaCuspSingleAtomReflectionScale 1 u) z) u := by
  have hcurv :=
    hasDerivAt_thetaCuspSingleAtomReflectionCurvature_scale hu hr
  have hslope := hasDerivAt_thetaCuspSingleAtomReflectionSlope_scale hu hr
  have hfirst := (hcurv.mul_const (z * (z + 2))).const_mul 4
  have hsecond := (hslope.mul_const (z + 1)).const_mul 4
  have hraw := hfirst.add hsecond
  have hfun :
      (fun x => thetaCuspSingleAtomReflectedActionJetTwo
        (thetaCuspSingleAtomReflectionScale 1 x) z) =
      (fun y => 4 *
        (thetaCuspSingleAtomReflectionLambda
            (thetaCuspSingleAtomReflectionScale 1 y) ^ (2 : ℕ) /
          thetaCuspSingleAtomReflectionFactor
            (thetaCuspSingleAtomReflectionScale 1 y) z ^ (2 : ℕ) *
          (z * (z + 2)))) +
        fun y => 4 *
          (thetaCuspSingleAtomReflectionSlope
            (thetaCuspSingleAtomReflectionScale 1 y) z * (z + 1)) := by
    funext x
    unfold thetaCuspSingleAtomReflectedActionJetTwo
    dsimp only
    simp only [Pi.add_apply]
    ring
  rw [hfun]
  apply hraw.congr_deriv
  unfold c5SingleAtomScaleMixedJetTwo
  dsimp only
  ring

/-- The exact logarithmic correction lies below its endpoint tangent. -/
theorem thetaCuspSingleAtomReflectedAction_le_defect_mul_slope
    {A t : ℝ} (hA : 3 < A) (ht : 0 < t)
    (hr : 0 < thetaCuspSingleAtomReflectionFactor A
      (thetaCuspSingleAtomReflectionDefect t)) :
    thetaCuspSingleAtomReflectedAction A t ≤
      thetaCuspSingleAtomReflectionDefect t *
        thetaCuspSingleAtomReflectionSlope A
          (thetaCuspSingleAtomReflectionDefect t) := by
  let z := thetaCuspSingleAtomReflectionDefect t
  let l := thetaCuspSingleAtomReflectionLambda A
  let r := thetaCuspSingleAtomReflectionFactor A z
  have hz : 0 < z := by
    dsimp only [z, thetaCuspSingleAtomReflectionDefect]
    exact sub_pos.mpr (Real.one_lt_cosh.mpr (by linarith))
  have hl : 0 < l := by
    simpa only [l] using thetaCuspSingleAtomReflectionLambda_pos hA
  have hr0 : 0 < r := by simpa only [r, z] using hr
  have hrlt : r < 1 := by
    dsimp only [r, thetaCuspSingleAtomReflectionFactor]
    nlinarith [mul_pos hl hz]
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hr0)
  rw [Real.log_inv] at hlog
  have hinv : r⁻¹ - 1 = l * z / r := by
    have hone : 1 - r = l * z := by
      dsimp only [r, l, thetaCuspSingleAtomReflectionFactor]
      ring
    calc
      r⁻¹ - 1 = (1 - r) / r := by
        rw [inv_eq_one_div]
        field_simp [hr0.ne']
      _ = l * z / r := by rw [hone]
  have hlogbound : -Real.log r ≤ l * z / r := by
    rw [← hinv]
    exact hlog
  calc
    thetaCuspSingleAtomReflectedAction A t =
        2 * A * z + (-Real.log r) := by
      unfold thetaCuspSingleAtomReflectedAction
      dsimp only [z, r]
      ring
    _ ≤ 2 * A * z + l * z / r := by nlinarith
    _ = z * thetaCuspSingleAtomReflectionSlope A z := by
      unfold thetaCuspSingleAtomReflectionSlope
      dsimp only [l, r]
      ring

private theorem two_mul_reflectionDefect_lt_self_mul_defectJet
    {t : ℝ} (ht : 0 < t) :
    2 * thetaCuspSingleAtomReflectionDefect t <
      t * (2 * Real.sinh (2 * t)) := by
  have hs := sinh_lt_mul_cosh ht
  have hspos : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hmul := mul_lt_mul_of_pos_left hs
    (mul_pos (by norm_num : (0 : ℝ) < 4) hspos)
  unfold thetaCuspSingleAtomReflectionDefect
  rw [Real.cosh_two_mul, Real.sinh_two_mul, Real.cosh_sq]
  nlinarith

/-- Exact first-atom action velocity is strictly superquadratic in displacement. -/
theorem two_mul_thetaCuspSingleAtomReflectedAction_lt_velocity
    {A t : ℝ} (hA : 3 < A) (ht : 0 < t)
    (hr : 0 < thetaCuspSingleAtomReflectionFactor A
      (thetaCuspSingleAtomReflectionDefect t)) :
    2 * thetaCuspSingleAtomReflectedAction A t <
      t * thetaCuspSingleAtomReflectedActionJetOne A
        (thetaCuspSingleAtomReflectionDefect t)
        (2 * Real.sinh (2 * t)) := by
  let z := thetaCuspSingleAtomReflectionDefect t
  let p := thetaCuspSingleAtomReflectionSlope A z
  have hqp := thetaCuspSingleAtomReflectedAction_le_defect_mul_slope
    hA ht hr
  have hp : 0 < p := by
    dsimp only [p, thetaCuspSingleAtomReflectionSlope]
    have hl := thetaCuspSingleAtomReflectionLambda_pos hA
    positivity
  have hz := two_mul_reflectionDefect_lt_self_mul_defectJet ht
  have hstrict := mul_lt_mul_of_pos_right hz hp
  unfold thetaCuspSingleAtomReflectedActionJetOne
  dsimp only [z, p] at hqp hstrict ⊢
  nlinarith

/-- The Bose weight lower barrier is stable under every superquadratic positive action. -/
theorem thirty_add_twelve_mul_lt_c5BoseWeight_of_superquadratic
    {q v : ℝ} (hq : 0 < q) (hv : 2 * q < v) :
    30 + 12 * q <
      14 + 10 * v + 8 * v / (Real.exp q - 1) := by
  have hr : 0 < Real.exp q - 1 := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hq
  have hcoeff : 0 < 10 + 8 / (Real.exp q - 1) := by positivity
  have hvw := mul_lt_mul_of_pos_right hv hcoeff
  have hBose :=
    eight_add_six_mul_lt_ten_mul_add_eight_mul_div_exp_sub_one hq
  calc
    30 + 12 * q = 14 + 2 * (8 + 6 * q) := by ring
    _ < 14 + 2 * (10 * q + 8 * q / (Real.exp q - 1)) := by nlinarith
    _ = 14 + (2 * q) * (10 + 8 / (Real.exp q - 1)) := by
      field_simp [hr.ne']
    _ < 14 + v * (10 + 8 / (Real.exp q - 1)) := by linarith
    _ = 14 + 10 * v + 8 * v / (Real.exp q - 1) := by
      field_simp [hr.ne']
      ring

/-- Exact first atom inherits the same `30+72z` compensation-weight floor as its Gaussian core. -/
theorem thirty_add_seventyTwo_mul_defect_lt_exactFirstAtomC5Weight
    {A t : ℝ} (hA : 3 < A) (ht : 0 < t)
    (hr : 0 < thetaCuspSingleAtomReflectionFactor A
      (thetaCuspSingleAtomReflectionDefect t)) :
    30 + 72 * thetaCuspSingleAtomReflectionDefect t <
      14 +
        10 * (t * thetaCuspSingleAtomReflectedActionJetOne A
          (thetaCuspSingleAtomReflectionDefect t)
          (2 * Real.sinh (2 * t))) +
        8 * (t * thetaCuspSingleAtomReflectedActionJetOne A
          (thetaCuspSingleAtomReflectionDefect t)
          (2 * Real.sinh (2 * t))) /
          (Real.exp (thetaCuspSingleAtomReflectedAction A t) - 1) := by
  let z := thetaCuspSingleAtomReflectionDefect t
  let q := thetaCuspSingleAtomReflectedAction A t
  let v := t * thetaCuspSingleAtomReflectedActionJetOne A z
    (2 * Real.sinh (2 * t))
  have hz : 0 < z := by
    dsimp only [z, thetaCuspSingleAtomReflectionDefect]
    exact sub_pos.mpr (Real.one_lt_cosh.mpr (by linarith))
  have hl := thetaCuspSingleAtomReflectionLambda_pos hA
  have hrlt : thetaCuspSingleAtomReflectionFactor A z < 1 := by
    unfold thetaCuspSingleAtomReflectionFactor
    nlinarith [mul_pos hl hz]
  have hlog : Real.log (thetaCuspSingleAtomReflectionFactor A z) < 0 :=
    Real.log_neg hr hrlt
  have hqGaussian : 2 * A * z < q := by
    dsimp only [q, thetaCuspSingleAtomReflectedAction]
    linarith
  have hq : 0 < q := lt_trans (by positivity) hqGaussian
  have hv : 2 * q < v := by
    dsimp only [q, v, z]
    exact two_mul_thetaCuspSingleAtomReflectedAction_lt_velocity hA ht hr
  have hweight :=
    thirty_add_twelve_mul_lt_c5BoseWeight_of_superquadratic hq hv
  dsimp only [q, v, z] at hweight ⊢
  have hqz : 6 * thetaCuspSingleAtomReflectionDefect t <
      thetaCuspSingleAtomReflectedAction A t := by
    nlinarith
  nlinarith

/-- Literal fixed-action centre transport numerator for exact first atom. -/
def c5SingleAtomVelocityCenterNumerator (A t : ℝ) : ℝ :=
  let z := thetaCuspSingleAtomReflectionDefect t
  let z' := 2 * Real.sinh (2 * t)
  let a := thetaCuspSingleAtomReflectedActionJetOne A z z'
  let b := thetaCuspSingleAtomReflectedActionJetTwo A z
  let s := c5SingleAtomScaleActionJetOne A z
  let m := c5SingleAtomScaleMixedJetOne A z z'
  a * (t * m) - (a + t * b) * s

/-- Literal velocity--slope fixed-action transport numerator for exact first atom. -/
def c5SingleAtomVelocitySlopeCenterNumerator (A t : ℝ) : ℝ :=
  let z := thetaCuspSingleAtomReflectionDefect t
  let z' := 2 * Real.sinh (2 * t)
  let a := thetaCuspSingleAtomReflectedActionJetOne A z z'
  let b := thetaCuspSingleAtomReflectedActionJetTwo A z
  let c := thetaCuspSingleAtomReflectedActionJetThree A z z'
  let s := c5SingleAtomScaleActionJetOne A z
  let m := c5SingleAtomScaleMixedJetOne A z z'
  let n := c5SingleAtomScaleMixedJetTwo A z
  a * (t * m + t ^ (2 : ℕ) * n) - (a + 3 * t * b + t ^ (2 : ℕ) * c) * s

/-- Full exact first-atom direct-C5 compensation margin. -/
def c5SingleAtomCompensationMargin (A t : ℝ) : ℝ :=
  let z := thetaCuspSingleAtomReflectionDefect t
  let z' := 2 * Real.sinh (2 * t)
  let q := thetaCuspSingleAtomReflectedAction A t
  let v := t * thetaCuspSingleAtomReflectedActionJetOne A z z'
  let H := c5SingleAtomVelocityCenterNumerator A t
  let P := c5SingleAtomVelocitySlopeCenterNumerator A t
  5 * P - (14 + 10 * v + 8 * v / (Real.exp q - 1)) * H

/-- Rational-hyperbolic base margin after replacing Bose weight by its exact global floor. -/
def c5SingleAtomBaseCompensationMargin (A t : ℝ) : ℝ :=
  let z := thetaCuspSingleAtomReflectionDefect t
  let H := c5SingleAtomVelocityCenterNumerator A t
  let P := c5SingleAtomVelocitySlopeCenterNumerator A t
  5 * P - (30 + 72 * z) * H

/-- Once centre transport is negative, exact Bose weight improves the rational base margin. -/
theorem c5SingleAtomBaseCompensationMargin_lt_full
    {A t : ℝ} (hA : 3 < A) (ht : 0 < t)
    (hr : 0 < thetaCuspSingleAtomReflectionFactor A
      (thetaCuspSingleAtomReflectionDefect t))
    (hH : c5SingleAtomVelocityCenterNumerator A t < 0) :
    c5SingleAtomBaseCompensationMargin A t <
      c5SingleAtomCompensationMargin A t := by
  let z := thetaCuspSingleAtomReflectionDefect t
  let z' := 2 * Real.sinh (2 * t)
  let q := thetaCuspSingleAtomReflectedAction A t
  let v := t * thetaCuspSingleAtomReflectedActionJetOne A z z'
  let H := c5SingleAtomVelocityCenterNumerator A t
  let P := c5SingleAtomVelocitySlopeCenterNumerator A t
  let W := 14 + 10 * v + 8 * v / (Real.exp q - 1)
  have hW := thirty_add_seventyTwo_mul_defect_lt_exactFirstAtomC5Weight
    hA ht hr
  have hWH : W * H < (30 + 72 * z) * H := by
    exact mul_lt_mul_of_neg_right (by
      dsimp only [W, q, v, z, z']
      exact hW) (by simpa only [H] using hH)
  unfold c5SingleAtomBaseCompensationMargin
    c5SingleAtomCompensationMargin
  dsimp only [z, z', q, v, H, P, W] at hWH ⊢
  linarith

/-- Exact first-atom compensation follows from the now purely rational-hyperbolic base sign. -/
theorem c5SingleAtomCompensationMargin_pos_of_base
    {A t : ℝ} (hA : 3 < A) (ht : 0 < t)
    (hr : 0 < thetaCuspSingleAtomReflectionFactor A
      (thetaCuspSingleAtomReflectionDefect t))
    (hH : c5SingleAtomVelocityCenterNumerator A t < 0)
    (hbase : 0 < c5SingleAtomBaseCompensationMargin A t) :
    0 < c5SingleAtomCompensationMargin A t :=
  lt_trans hbase
    (c5SingleAtomBaseCompensationMargin_lt_full hA ht hr hH)

private theorem four_mul_add_two_lambdaJet_pos
    {A : ℝ} (hA : 6 ≤ A) :
    0 < 4 * A + 2 * c5SingleAtomScaleLambdaJetOne A := by
  let b := A - 3 / 2
  have hb : 9 / 2 ≤ b := by dsimp only [b]; linarith
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hb2 : (81 / 4 : ℝ) ≤ b ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (b - 9 / 2)]
  have hmul : b * (81 / 4 : ℝ) ≤ b * b ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hb2 hb0.le
  have hlinear : 3 * b + 9 < b * (81 / 4 : ℝ) := by nlinarith
  have hgap : 0 < b ^ (3 : ℕ) - 3 * (b + 3) := by
    nlinarith [show b * b ^ (2 : ℕ) = b ^ (3 : ℕ) by ring]
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hden : 0 < (A - 3 / 2) ^ (3 : ℕ) := by positivity
  have hid :
      4 * A + 2 * c5SingleAtomScaleLambdaJetOne A =
        4 * A * ((A - 3 / 2) ^ (3 : ℕ) - 3 * (A + 3 / 2)) /
          (A - 3 / 2) ^ (3 : ℕ) := by
    apply (eq_div_iff hden.ne').2
    have hdprod :
        c5SingleAtomScaleLambdaJetOne A * (A - 3 / 2) ^ (3 : ℕ) =
          -6 * A * (A + 3 / 2) := by
      unfold c5SingleAtomScaleLambdaJetOne
      exact div_mul_cancel₀ _ hden.ne'
    calc
      (4 * A + 2 * c5SingleAtomScaleLambdaJetOne A) *
          (A - 3 / 2) ^ (3 : ℕ) =
        4 * A * (A - 3 / 2) ^ (3 : ℕ) +
          2 * (c5SingleAtomScaleLambdaJetOne A *
            (A - 3 / 2) ^ (3 : ℕ)) := by ring
      _ = 4 * A * (A - 3 / 2) ^ (3 : ℕ) - 12 * A * (A + 3 / 2) := by
        rw [hdprod]
        ring
      _ = 4 * A * ((A - 3 / 2) ^ (3 : ℕ) - 3 * (A + 3 / 2)) := by ring
  rw [hid]
  have hgapA : 0 < (A - 3 / 2) ^ (3 : ℕ) - 3 * (A + 3 / 2) := by
    dsimp only [b] at hgap
    have hshift : A + 3 / 2 = (A - 3 / 2) + 3 := by ring
    simpa only [hshift] using hgap
  positivity

private theorem c5SingleAtomScaleActionSlope_pos
    {A z : ℝ} (hA : 6 ≤ A)
    (hrhalf : 1 / 2 < thetaCuspSingleAtomReflectionFactor A z) :
    0 < 4 * A + c5SingleAtomScaleLambdaJetOne A /
      thetaCuspSingleAtomReflectionFactor A z := by
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  have hd : d < 0 := by
    dsimp only [d]
    exact c5SingleAtomScaleLambdaJetOne_neg (lt_of_lt_of_le (by norm_num) hA)
  have hr : 0 < r := by
    dsimp only [r]
    linarith
  have hinv : 1 / r < 2 := by
    rw [div_lt_iff₀ hr]
    dsimp only [r]
    nlinarith
  have hmul := mul_lt_mul_of_neg_left hinv hd
  have hmul' : 2 * d < d / r := by
    rw [div_eq_mul_inv]
    simpa only [one_div, mul_comm] using hmul
  have hbase := four_mul_add_two_lambdaJet_pos hA
  dsimp only [d, r] at hmul' ⊢
  nlinarith

/-- In the structural tail chamber `A≥6`, exact first-atom fixed-action centre transport is
strictly negative. The proof uses the coefficient's exact scale contraction, not a numerical
smallness estimate. -/
theorem c5SingleAtomVelocityCenterNumerator_neg
    {A t : ℝ} (hA : 6 ≤ A) (ht : 0 < t)
    (hrhalf : 1 / 2 < thetaCuspSingleAtomReflectionFactor A
      (thetaCuspSingleAtomReflectionDefect t)) :
    c5SingleAtomVelocityCenterNumerator A t < 0 := by
  let z := thetaCuspSingleAtomReflectionDefect t
  let z' := 2 * Real.sinh (2 * t)
  let l := thetaCuspSingleAtomReflectionLambda A
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let p := 2 * A + l / r
  let g := l ^ (2 : ℕ) / r ^ (2 : ℕ)
  let L := 4 * A + d / r
  let M := 4 * A + d / r ^ (2 : ℕ)
  have hz : 0 < z := by
    dsimp only [z, thetaCuspSingleAtomReflectionDefect]
    exact sub_pos.mpr (Real.one_lt_cosh.mpr (by linarith))
  have hz' : 0 < z' := by
    dsimp only [z']
    positivity
  have hl : 0 < l := by
    dsimp only [l]
    exact thetaCuspSingleAtomReflectionLambda_pos
      (lt_of_lt_of_le (by norm_num) hA)
  have hr : 0 < r := by
    dsimp only [r, z]
    linarith
  have hrlt : r < 1 := by
    dsimp only [r, thetaCuspSingleAtomReflectionFactor]
    nlinarith [mul_pos hl hz]
  have hd : d < 0 := by
    dsimp only [d]
    exact c5SingleAtomScaleLambdaJetOne_neg
      (lt_of_lt_of_le (by norm_num) hA)
  have hp : 0 < p := by dsimp only [p]; positivity
  have hg : 0 < g := by dsimp only [g]; positivity
  have hL : 0 < L := by
    dsimp only [L, d, r]
    exact c5SingleAtomScaleActionSlope_pos hA hrhalf
  have hr2lt : r ^ (2 : ℕ) < r := by
    nlinarith [mul_pos hr (sub_pos.mpr hrlt)]
  have hscaled := mul_lt_mul_of_neg_left hr2lt hd
  have hML : M < L := by
    have hdiv : d / r ^ (2 : ℕ) < d / r := by
      rw [div_lt_div_iff₀ (sq_pos_of_pos hr) hr]
      simpa only [mul_comm] using hscaled
    dsimp only [M, L]
    linarith
  have hfour : 4 * t - z' < 0 := by
    dsimp only [z']
    have hs := self_lt_sinh (by linarith : 0 < 2 * t)
    linarith
  have hfactor :
      c5SingleAtomVelocityCenterNumerator A t =
        z * (4 * t * p * (z + 2) * M - p * z' * L -
          4 * t * (g * z * (z + 2) + p * (z + 1)) * L) := by
    have ha :
        thetaCuspSingleAtomReflectedActionJetOne A z z' = p * z' := by
      unfold thetaCuspSingleAtomReflectedActionJetOne
        thetaCuspSingleAtomReflectionSlope
      dsimp only [p, l, r]
    have hb :
        thetaCuspSingleAtomReflectedActionJetTwo A z =
          4 * (g * z * (z + 2) + p * (z + 1)) := by
      unfold thetaCuspSingleAtomReflectedActionJetTwo
        thetaCuspSingleAtomReflectionSlope
      dsimp only [g, p, l, r]
      ring
    have hs : c5SingleAtomScaleActionJetOne A z = z * L := by
      unfold c5SingleAtomScaleActionJetOne
      dsimp only [L, d, r]
      ring
    have hm : c5SingleAtomScaleMixedJetOne A z z' = M * z' := by
      unfold c5SingleAtomScaleMixedJetOne
      dsimp only [M, d, r]
    have hzsq : (2 * Real.sinh (2 * t)) ^ (2 : ℕ) =
        4 * thetaCuspSingleAtomReflectionDefect t *
          (thetaCuspSingleAtomReflectionDefect t + 2) :=
      sq_two_mul_sinh_two t
    unfold c5SingleAtomVelocityCenterNumerator
    dsimp only
    rw [ha, hb, hs, hm]
    have hzsq' : z' ^ (2 : ℕ) = 4 * z * (z + 2) := by
      simpa only [z, z'] using hzsq
    calc
      p * z' * (t * (M * z')) -
          (p * z' + t * (4 * (g * z * (z + 2) + p * (z + 1)))) *
            (z * L) =
        t * p * M * z' ^ (2 : ℕ) - p * z' * z * L -
          4 * t * (g * z * (z + 2) + p * (z + 1)) * z * L := by ring
      _ = z * (4 * t * p * (z + 2) * M - p * z' * L -
          4 * t * (g * z * (z + 2) + p * (z + 1)) * L) := by
        rw [hzsq']
        ring
  have hlead :
      4 * t * p * (z + 2) * M < 4 * t * p * (z + 2) * L := by
    exact mul_lt_mul_of_pos_left hML (by positivity)
  have hbracket :
      4 * t * p * (z + 2) * M - p * z' * L -
          4 * t * (g * z * (z + 2) + p * (z + 1)) * L < 0 := by
    have hnegative :
        p * (4 * t - z') - 4 * t * g * z * (z + 2) < 0 := by
      have hpneg : p * (4 * t - z') < 0 := mul_neg_of_pos_of_neg hp hfour
      have hcorr : 0 < 4 * t * g * z * (z + 2) := by positivity
      linarith
    have htarget :
        4 * t * p * (z + 2) * L - p * z' * L -
            4 * t * (g * z * (z + 2) + p * (z + 1)) * L < 0 := by
      nlinarith [mul_neg_of_pos_of_neg hL hnegative]
    linarith
  rw [hfactor]
  exact mul_neg_of_pos_of_neg hz hbracket

/-- Physical same-half-line form of exact first-atom centre-transport negativity. -/
theorem c5SingleAtomVelocityCenterNumerator_neg_of_sameHalfLine
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    c5SingleAtomVelocityCenterNumerator
      (thetaCuspSingleAtomReflectionScale 1 u) t < 0 :=
  c5SingleAtomVelocityCenterNumerator_neg hscale ht
    (one_half_lt_thetaCuspSingleAtomReflectionFactor_of_sameHalfLine
      ht.le htu)

end

end RHTower
