import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeSource

/-!
# Reflected Riccati contraction for one theta-cusp atom

Every positive theta-cusp source atom has a strictly contracting reflected logarithmic curvature
on a single modular half-line.  The proof is the exact polynomial--Gaussian normal form and
rational inequalities; it uses neither the completed atom sum nor zero data.
-/

open Set

namespace RHTower

noncomputable section

/-- Natural exponential scale of one theta-cusp atom. -/
def thetaCuspSingleAtomReflectionScale (n : ℕ) (u : ℝ) : ℝ :=
  Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)

theorem three_lt_thetaCuspSingleAtomReflectionScale
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u) :
    3 < thetaCuspSingleAtomReflectionScale n u := by
  unfold thetaCuspSingleAtomReflectionScale
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnSq : 1 ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have he : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hprod : 1 ≤ (n : ℝ) ^ 2 * Real.exp (2 * u) :=
    one_le_mul_of_one_le_of_one_le hnSq he
  have hpi :
      Real.pi ≤ Real.pi * ((n : ℝ) ^ 2 * Real.exp (2 * u)) :=
    le_mul_of_one_le_right Real.pi_pos.le hprod
  nlinarith [Real.pi_gt_three]

/-- Hyperbolic displacement variable in the reflected atom product. -/
def thetaCuspSingleAtomReflectionDefect (t : ℝ) : ℝ :=
  Real.cosh (2 * t) - 1

/-- Rational coefficient in the normalized reflected atom product. -/
def thetaCuspSingleAtomReflectionLambda (A : ℝ) : ℝ :=
  3 * A / (A - 3 / 2) ^ 2

/-- Positive polynomial factor in the normalized reflected atom product. -/
def thetaCuspSingleAtomReflectionFactor (A z : ℝ) : ℝ :=
  1 - thetaCuspSingleAtomReflectionLambda A * z

/-- Exact normalized model profile of one reflected theta atom. -/
def thetaCuspSingleAtomReflectedNormalizedModel (A z : ℝ) : ℝ :=
  thetaCuspSingleAtomReflectionFactor A z * Real.exp (-2 * A * z)

/-- Negative logarithm of the normalized reflected atom model along its hyperbolic path. -/
def thetaCuspSingleAtomReflectedAction (A t : ℝ) : ℝ :=
  2 * A * thetaCuspSingleAtomReflectionDefect t -
    Real.log (thetaCuspSingleAtomReflectionFactor A
      (thetaCuspSingleAtomReflectionDefect t))

/-- Logarithmic slope with respect to the hyperbolic defect variable. -/
def thetaCuspSingleAtomReflectionSlope (A z : ℝ) : ℝ :=
  2 * A + thetaCuspSingleAtomReflectionLambda A /
    thetaCuspSingleAtomReflectionFactor A z

/-- First displacement jet of the reflected logarithmic action. -/
def thetaCuspSingleAtomReflectedActionJetOne (A z z' : ℝ) : ℝ :=
  thetaCuspSingleAtomReflectionSlope A z * z'

/-- Second displacement jet of the reflected logarithmic action. -/
def thetaCuspSingleAtomReflectedActionJetTwo (A z : ℝ) : ℝ :=
  let l := thetaCuspSingleAtomReflectionLambda A
  let r := thetaCuspSingleAtomReflectionFactor A z
  4 * (l ^ 2 / r ^ 2) * z * (z + 2) +
    4 * thetaCuspSingleAtomReflectionSlope A z * (z + 1)

/-- Third displacement jet of the reflected logarithmic action. -/
def thetaCuspSingleAtomReflectedActionJetThree (A z z' : ℝ) : ℝ :=
  let l := thetaCuspSingleAtomReflectionLambda A
  let r := thetaCuspSingleAtomReflectionFactor A z
  z' * (8 * (l ^ 3 / r ^ 3) * z * (z + 2) +
    12 * (l ^ 2 / r ^ 2) * (z + 1) +
      4 * thetaCuspSingleAtomReflectionSlope A z)

/-- The reflected Riccati margin `2 q q' - q''` in exact defect coordinates. -/
def thetaCuspSingleAtomReflectedRiccatiMargin (A z z' : ℝ) : ℝ :=
  2 * thetaCuspSingleAtomReflectedActionJetOne A z z' *
      thetaCuspSingleAtomReflectedActionJetTwo A z -
    thetaCuspSingleAtomReflectedActionJetThree A z z'

/-- Reduced rational margin after extracting the positive hyperbolic velocity. -/
def thetaCuspSingleAtomReflectedReducedMargin (A z : ℝ) : ℝ :=
  let l := thetaCuspSingleAtomReflectionLambda A
  let r := thetaCuspSingleAtomReflectionFactor A z
  l ^ 2 / r ^ 2 * (4 * A * z * (z + 2) - (z + 1)) +
    8 * A ^ 2 * (z + 1) - 2 * A +
      (8 * A * (z + 1) - 1) * l / r

/-- The reflected action is literally the negative logarithm of the normalized model. -/
theorem thetaCuspSingleAtomReflectedAction_eq_neg_log_model
    {A t : ℝ}
    (hr : thetaCuspSingleAtomReflectionFactor A
      (thetaCuspSingleAtomReflectionDefect t) ≠ 0) :
    thetaCuspSingleAtomReflectedAction A t =
      -Real.log (thetaCuspSingleAtomReflectedNormalizedModel A
        (thetaCuspSingleAtomReflectionDefect t)) := by
  unfold thetaCuspSingleAtomReflectedAction
    thetaCuspSingleAtomReflectedNormalizedModel
  rw [Real.log_mul hr (Real.exp_pos _).ne', Real.log_exp]
  ring

theorem hasDerivAt_thetaCuspSingleAtomReflectionDefect (t : ℝ) :
    HasDerivAt thetaCuspSingleAtomReflectionDefect
      (2 * Real.sinh (2 * t)) t := by
  have hraw := ((Real.hasDerivAt_cosh (2 * t)).comp t
    ((hasDerivAt_id t).const_mul 2)).sub_const 1
  have hfun :
      thetaCuspSingleAtomReflectionDefect =
        fun x : ℝ => (Real.cosh ∘ fun y : ℝ => 2 * id y) x - 1 := by
    funext x
    rfl
  rw [hfun]
  exact hraw.congr_deriv (by ring)

theorem hasDerivAt_two_mul_sinh_two (t : ℝ) :
    HasDerivAt (fun x : ℝ => 2 * Real.sinh (2 * x))
      (4 * (thetaCuspSingleAtomReflectionDefect t + 1)) t := by
  have h := ((Real.hasDerivAt_sinh (2 * t)).comp t
    ((hasDerivAt_id t).const_mul 2)).const_mul 2
  have hfun :
      (fun x : ℝ => 2 * Real.sinh (2 * x)) =
        fun x => 2 * (Real.sinh ∘ fun y : ℝ => 2 * id y) x := by
    funext x
    rfl
  rw [hfun]
  apply h.congr_deriv
  unfold thetaCuspSingleAtomReflectionDefect
  ring

theorem sq_two_mul_sinh_two (t : ℝ) :
    (2 * Real.sinh (2 * t)) ^ 2 =
      4 * thetaCuspSingleAtomReflectionDefect t *
        (thetaCuspSingleAtomReflectionDefect t + 2) := by
  rw [show (2 * Real.sinh (2 * t)) ^ 2 =
      4 * Real.sinh (2 * t) ^ 2 by ring, Real.sinh_sq]
  unfold thetaCuspSingleAtomReflectionDefect
  ring

theorem hasDerivAt_thetaCuspSingleAtomReflectionFactor
    (A t : ℝ) :
    HasDerivAt
      (fun x => thetaCuspSingleAtomReflectionFactor A
        (thetaCuspSingleAtomReflectionDefect x))
      (-thetaCuspSingleAtomReflectionLambda A * (2 * Real.sinh (2 * t))) t := by
  have hz := hasDerivAt_thetaCuspSingleAtomReflectionDefect t
  have hraw :=
    (hz.const_mul (-thetaCuspSingleAtomReflectionLambda A)).const_add 1
  have hfun :
      (fun x => thetaCuspSingleAtomReflectionFactor A
        (thetaCuspSingleAtomReflectionDefect x)) =
        fun x => 1 + (-thetaCuspSingleAtomReflectionLambda A) *
          thetaCuspSingleAtomReflectionDefect x := by
    funext x
    unfold thetaCuspSingleAtomReflectionFactor
    ring
  rw [hfun]
  exact hraw.congr_deriv (by ring)

theorem hasDerivAt_thetaCuspSingleAtomReflectionSlope
    {A t : ℝ}
    (hr : thetaCuspSingleAtomReflectionFactor A
      (thetaCuspSingleAtomReflectionDefect t) ≠ 0) :
    HasDerivAt
      (fun x => thetaCuspSingleAtomReflectionSlope A
        (thetaCuspSingleAtomReflectionDefect x))
      (thetaCuspSingleAtomReflectionLambda A ^ 2 /
        thetaCuspSingleAtomReflectionFactor A
          (thetaCuspSingleAtomReflectionDefect t) ^ 2 *
            (2 * Real.sinh (2 * t))) t := by
  let l := thetaCuspSingleAtomReflectionLambda A
  have hrDeriv := hasDerivAt_thetaCuspSingleAtomReflectionFactor A t
  have hquot := (hasDerivAt_const t l).fun_div hrDeriv hr
  have hraw := hquot.const_add (2 * A)
  have hfun :
      (fun x => thetaCuspSingleAtomReflectionSlope A
        (thetaCuspSingleAtomReflectionDefect x)) =
        fun x => 2 * A + l /
          thetaCuspSingleAtomReflectionFactor A
            (thetaCuspSingleAtomReflectionDefect x) := by
    funext x
    rfl
  rw [hfun]
  apply hraw.congr_deriv
  dsimp only [l]
  field_simp [hr]
  ring

theorem hasDerivAt_thetaCuspSingleAtomReflectionCurvature
    {A t : ℝ}
    (hr : thetaCuspSingleAtomReflectionFactor A
      (thetaCuspSingleAtomReflectionDefect t) ≠ 0) :
    HasDerivAt
      (fun x =>
        thetaCuspSingleAtomReflectionLambda A ^ 2 /
          thetaCuspSingleAtomReflectionFactor A
            (thetaCuspSingleAtomReflectionDefect x) ^ 2)
      (2 * thetaCuspSingleAtomReflectionLambda A ^ 3 /
        thetaCuspSingleAtomReflectionFactor A
          (thetaCuspSingleAtomReflectionDefect t) ^ 3 *
            (2 * Real.sinh (2 * t))) t := by
  have hrDeriv := hasDerivAt_thetaCuspSingleAtomReflectionFactor A t
  have hquot := (hasDerivAt_const t
    (thetaCuspSingleAtomReflectionLambda A)).fun_div hrDeriv hr
  have hsquare := hquot.pow 2
  have hfun :
      (fun x =>
        thetaCuspSingleAtomReflectionLambda A ^ 2 /
          thetaCuspSingleAtomReflectionFactor A
            (thetaCuspSingleAtomReflectionDefect x) ^ 2) =
        (fun x => thetaCuspSingleAtomReflectionLambda A /
          thetaCuspSingleAtomReflectionFactor A
            (thetaCuspSingleAtomReflectionDefect x)) ^ 2 := by
    funext x
    simp only [Pi.pow_apply, div_pow]
  rw [hfun]
  apply hsquare.congr_deriv
  simp only [Nat.cast_ofNat, zero_mul, zero_sub]
  norm_num
  field_simp [hr]

/-- The first displayed jet is the literal first derivative of the reflected action. -/
theorem hasDerivAt_thetaCuspSingleAtomReflectedAction
    {A t : ℝ}
    (hr : thetaCuspSingleAtomReflectionFactor A
      (thetaCuspSingleAtomReflectionDefect t) ≠ 0) :
    HasDerivAt (thetaCuspSingleAtomReflectedAction A)
      (thetaCuspSingleAtomReflectedActionJetOne A
        (thetaCuspSingleAtomReflectionDefect t) (2 * Real.sinh (2 * t))) t := by
  have hz := hasDerivAt_thetaCuspSingleAtomReflectionDefect t
  have hrDeriv := hasDerivAt_thetaCuspSingleAtomReflectionFactor A t
  have hmain := (hz.const_mul (2 * A)).sub (hrDeriv.log hr)
  have hfun :
      thetaCuspSingleAtomReflectedAction A =
        (fun x => 2 * A * thetaCuspSingleAtomReflectionDefect x) -
          fun x => Real.log (thetaCuspSingleAtomReflectionFactor A
            (thetaCuspSingleAtomReflectionDefect x)) := by
    funext x
    rfl
  rw [hfun]
  apply hmain.congr_deriv
  unfold thetaCuspSingleAtomReflectedActionJetOne
    thetaCuspSingleAtomReflectionSlope
  field_simp [hr]
  ring

/-- The second displayed jet is the literal derivative of the first reflected action jet. -/
theorem hasDerivAt_thetaCuspSingleAtomReflectedActionJetOne
    {A t : ℝ}
    (hr : thetaCuspSingleAtomReflectionFactor A
      (thetaCuspSingleAtomReflectionDefect t) ≠ 0) :
    HasDerivAt
      (fun x => thetaCuspSingleAtomReflectedActionJetOne A
        (thetaCuspSingleAtomReflectionDefect x) (2 * Real.sinh (2 * x)))
      (thetaCuspSingleAtomReflectedActionJetTwo A
        (thetaCuspSingleAtomReflectionDefect t)) t := by
  have hz := hasDerivAt_thetaCuspSingleAtomReflectionDefect t
  have hz' := hasDerivAt_two_mul_sinh_two t
  have hslope := hasDerivAt_thetaCuspSingleAtomReflectionSlope hr
  have hraw := hslope.mul hz'
  have hfun :
      (fun x => thetaCuspSingleAtomReflectedActionJetOne A
        (thetaCuspSingleAtomReflectionDefect x) (2 * Real.sinh (2 * x))) =
        (fun x => thetaCuspSingleAtomReflectionSlope A
          (thetaCuspSingleAtomReflectionDefect x)) *
            fun x => 2 * Real.sinh (2 * x) := by
    funext x
    rfl
  rw [hfun]
  apply hraw.congr_deriv
  unfold thetaCuspSingleAtomReflectedActionJetTwo
  rw [show
      thetaCuspSingleAtomReflectionLambda A ^ 2 /
            thetaCuspSingleAtomReflectionFactor A
              (thetaCuspSingleAtomReflectionDefect t) ^ 2 *
          (2 * Real.sinh (2 * t)) * (2 * Real.sinh (2 * t)) =
        thetaCuspSingleAtomReflectionLambda A ^ 2 /
            thetaCuspSingleAtomReflectionFactor A
              (thetaCuspSingleAtomReflectionDefect t) ^ 2 *
          (2 * Real.sinh (2 * t)) ^ 2 by ring,
    sq_two_mul_sinh_two t]
  ring

/-- The third displayed jet is the literal derivative of the second reflected action jet. -/
theorem hasDerivAt_thetaCuspSingleAtomReflectedActionJetTwo
    {A t : ℝ}
    (hr : thetaCuspSingleAtomReflectionFactor A
      (thetaCuspSingleAtomReflectionDefect t) ≠ 0) :
    HasDerivAt
      (fun x => thetaCuspSingleAtomReflectedActionJetTwo A
        (thetaCuspSingleAtomReflectionDefect x))
      (thetaCuspSingleAtomReflectedActionJetThree A
        (thetaCuspSingleAtomReflectionDefect t) (2 * Real.sinh (2 * t))) t := by
  have hz := hasDerivAt_thetaCuspSingleAtomReflectionDefect t
  have hslope := hasDerivAt_thetaCuspSingleAtomReflectionSlope hr
  have hcurvature := hasDerivAt_thetaCuspSingleAtomReflectionCurvature hr
  have hfirst := ((hcurvature.mul (hz.mul (hz.const_add 2))).const_mul 4)
  have hsecond := ((hslope.mul (hz.const_add 1)).const_mul 4)
  have hraw := hfirst.add hsecond
  have hfun :
      (fun x => thetaCuspSingleAtomReflectedActionJetTwo A
        (thetaCuspSingleAtomReflectionDefect x)) =
        (fun y =>
          4 * ((fun x =>
            thetaCuspSingleAtomReflectionLambda A ^ 2 /
              thetaCuspSingleAtomReflectionFactor A
                (thetaCuspSingleAtomReflectionDefect x) ^ 2) *
                  (thetaCuspSingleAtomReflectionDefect *
                    fun x => 2 + thetaCuspSingleAtomReflectionDefect x)) y) +
        fun y =>
          4 * ((fun x => thetaCuspSingleAtomReflectionSlope A
            (thetaCuspSingleAtomReflectionDefect x)) *
              fun x => 1 + thetaCuspSingleAtomReflectionDefect x) y := by
    funext x
    unfold thetaCuspSingleAtomReflectedActionJetTwo
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  rw [hfun]
  apply hraw.congr_deriv
  unfold thetaCuspSingleAtomReflectedActionJetThree
  simp only [Pi.mul_apply]
  field_simp [hr]
  ring

theorem thetaCuspSingleAtomReflectionLambda_pos
    {A : ℝ} (hA : 3 < A) :
    0 < thetaCuspSingleAtomReflectionLambda A := by
  unfold thetaCuspSingleAtomReflectionLambda
  have hden : 0 < (A - 3 / 2) ^ 2 := sq_pos_of_pos (by linarith)
  exact div_pos (mul_pos (by norm_num) (by linarith)) hden

theorem thetaCuspSingleAtomReflectionLambda_le_four
    {A : ℝ} (hA : 3 ≤ A) :
    thetaCuspSingleAtomReflectionLambda A ≤ 4 := by
  unfold thetaCuspSingleAtomReflectionLambda
  have hbase : 0 < A - 3 / 2 := by linarith
  have hden : 0 < (A - 3 / 2) ^ 2 := sq_pos_of_pos hbase
  apply (div_le_iff₀ hden).2
  have hfactor : 0 ≤ (A - 3) * (4 * A - 3) :=
    mul_nonneg (sub_nonneg.mpr hA) (by linarith)
  nlinarith

theorem thetaCuspSingleAtomReflectedRiccatiMargin_eq
    {A z z' : ℝ}
    (hr : thetaCuspSingleAtomReflectionFactor A z ≠ 0) :
    thetaCuspSingleAtomReflectedRiccatiMargin A z z' =
      4 * z' * thetaCuspSingleAtomReflectedReducedMargin A z := by
  unfold thetaCuspSingleAtomReflectedRiccatiMargin
    thetaCuspSingleAtomReflectedActionJetOne
    thetaCuspSingleAtomReflectedActionJetTwo
    thetaCuspSingleAtomReflectedActionJetThree
    thetaCuspSingleAtomReflectedReducedMargin
    thetaCuspSingleAtomReflectionSlope
  dsimp only
  field_simp [hr]
  ring

/-- The reduced reflected margin is strictly positive throughout the positive atom chamber. -/
theorem thetaCuspSingleAtomReflectedReducedMargin_pos
    {A z : ℝ} (hA : 3 < A) (hz : 0 ≤ z)
    (hr : 0 < thetaCuspSingleAtomReflectionFactor A z) :
    0 < thetaCuspSingleAtomReflectedReducedMargin A z := by
  let l := thetaCuspSingleAtomReflectionLambda A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let C := 4 * A * z * (z + 2) - (z + 1)
  have hl0 : 0 < l := by
    simpa only [l] using thetaCuspSingleAtomReflectionLambda_pos hA
  have hl4 : l ≤ 4 := by
    simpa only [l] using thetaCuspSingleAtomReflectionLambda_le_four hA.le
  have hr0 : 0 < r := by simpa only [r] using hr
  have hA0 : 0 < A := lt_trans (by norm_num) hA
  have hbase : 0 < 8 * A ^ 2 * (z + 1) - 2 * A := by
    nlinarith [sq_pos_of_pos hA0]
  have hlast : 0 < (8 * A * (z + 1) - 1) * l / r := by
    have hcoeff : 0 < 8 * A * (z + 1) - 1 := by
      nlinarith [mul_nonneg hA0.le hz]
    exact div_pos (mul_pos hcoeff hl0) hr0
  by_cases hC : 0 ≤ C
  · have hfirst : 0 ≤ l ^ 2 / r ^ 2 * C := by positivity
    have htarget : 0 < l ^ 2 / r ^ 2 * C +
        8 * A ^ 2 * (z + 1) - 2 * A +
          (8 * A * (z + 1) - 1) * l / r := by
      nlinarith
    simpa only [thetaCuspSingleAtomReflectedReducedMargin, l, r, C] using htarget
  · have hCneg : C < 0 := lt_of_not_ge hC
    have hz23 : z < 1 / 23 := by
      have hrough : (8 * A - 1) * z < 1 := by
        dsimp [C] at hCneg
        nlinarith [mul_nonneg hz (add_nonneg hz (by norm_num : (0 : ℝ) ≤ 2))]
      have hcoef : 23 < 8 * A - 1 := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hcoef.le) hz]
    have hlz : l * z < 4 / 23 := by
      have hzl : l * z ≤ 4 * z :=
        mul_le_mul_of_nonneg_right hl4 hz
      nlinarith [mul_pos (by norm_num : (0 : ℝ) < 23) (sub_pos.mpr hz23)]
    have hr19 : 19 / 23 < r := by
      dsimp [r, thetaCuspSingleAtomReflectionFactor]
      change 19 / 23 < 1 - l * z
      linarith
    have hz1 : z + 1 < 24 / 23 := by linarith
    have hlSq : l ^ 2 ≤ 16 := by nlinarith
    have hrSq : (19 / 23 : ℝ) ^ 2 < r ^ 2 := by
      nlinarith [sq_nonneg (r - 19 / 23)]
    have hnum : (z + 1) * l ^ 2 < (24 / 23 : ℝ) * 16 := by
      calc
        (z + 1) * l ^ 2 < (24 / 23) * l ^ 2 :=
          mul_lt_mul_of_pos_right hz1 (sq_pos_of_pos hl0)
        _ ≤ (24 / 23) * 16 := by gcongr
    have hquot : (z + 1) * l ^ 2 / r ^ 2 < 25 := by
      calc
        (z + 1) * l ^ 2 / r ^ 2 <
            ((24 / 23 : ℝ) * 16) / r ^ 2 :=
          div_lt_div_of_pos_right hnum (sq_pos_of_pos hr0)
        _ < ((24 / 23 : ℝ) * 16) / (19 / 23 : ℝ) ^ 2 := by
          exact div_lt_div_of_pos_left (by positivity) (by positivity) hrSq
        _ < 25 := by norm_num
    have hClo : -(z + 1) ≤ C := by
      have hnonneg : 0 ≤ 4 * A * z * (z + 2) := by positivity
      dsimp [C]
      linarith
    have hfirst : -25 < l ^ 2 / r ^ 2 * C := by
      have hscale0 : 0 ≤ l ^ 2 / r ^ 2 := by positivity
      have hmul :
          -(z + 1) * (l ^ 2 / r ^ 2) ≤ C * (l ^ 2 / r ^ 2) :=
        mul_le_mul_of_nonneg_right hClo hscale0
      have hrearrange :
          -(z + 1) * (l ^ 2 / r ^ 2) =
            -((z + 1) * l ^ 2 / r ^ 2) := by ring
      rw [hrearrange] at hmul
      nlinarith
    have hbase66 : 66 < 8 * A ^ 2 * (z + 1) - 2 * A := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hA.le) (by linarith : 0 ≤ 8 * A + 22)]
    have htarget : 0 < l ^ 2 / r ^ 2 * C +
        8 * A ^ 2 * (z + 1) - 2 * A +
          (8 * A * (z + 1) - 1) * l / r := by
      linarith
    simpa only [thetaCuspSingleAtomReflectedReducedMargin, l, r, C] using htarget

/-- Strict Riccati contraction of the exact reflected atom model. -/
theorem thetaCuspSingleAtomReflectedRiccatiMargin_pos
    {A z z' : ℝ} (hA : 3 < A) (hz : 0 ≤ z) (hz' : 0 < z')
    (hr : 0 < thetaCuspSingleAtomReflectionFactor A z) :
    0 < thetaCuspSingleAtomReflectedRiccatiMargin A z z' := by
  rw [thetaCuspSingleAtomReflectedRiccatiMargin_eq hr.ne']
  exact mul_pos (mul_pos (by norm_num) hz')
    (thetaCuspSingleAtomReflectedReducedMargin_pos hA hz hr)

/-- Closed polynomial--Gaussian form of one positive theta-cusp atom. -/
theorem thetaCuspSourceTerm_eq_singleAtomScale
    {n : ℕ} (x : ℝ) :
    thetaCuspSourceTerm x n =
      4 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * x / 2) *
        (thetaCuspSingleAtomReflectionScale n x - 3 / 2) *
          Real.exp (-thetaCuspSingleAtomReflectionScale n x) := by
  unfold thetaCuspSourceTerm thetaCuspSeed thetaCuspSingleAtomReflectionScale
  rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
    rw [show 2 * x = x + x by ring, Real.exp_add]
    ring]
  rw [show Real.exp (5 * x / 2) =
      Real.exp (x / 2) * Real.exp x ^ 2 by
    calc
      Real.exp (5 * x / 2) = Real.exp (x / 2 + 2 * x) := by
        congr 1
        ring
      _ = Real.exp (x / 2) * Real.exp (2 * x) := Real.exp_add _ _
      _ = Real.exp (x / 2) * Real.exp x ^ 2 := by
        rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
          rw [show 2 * x = x + x by ring, Real.exp_add]
          ring]]
  ring_nf

/-- Exact reflected-product form of one source atom on one modular half-line. -/
theorem thetaCuspSourceTerm_reflected_mul_eq_singleAtomModel
    {n : ℕ} (hn : 0 < n) {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) n =
      thetaCuspSourceTerm u n ^ 2 *
        thetaCuspSingleAtomReflectedNormalizedModel
          (thetaCuspSingleAtomReflectionScale n u)
          (thetaCuspSingleAtomReflectionDefect t) := by
  let A := thetaCuspSingleAtomReflectionScale n u
  let z := thetaCuspSingleAtomReflectionDefect t
  let e := Real.exp (2 * t)
  have hu : 0 ≤ u := le_trans ht htu
  have hA : 3 < A := by
    simpa only [A] using three_lt_thetaCuspSingleAtomReflectionScale hn hu
  have hA32 : A - 3 / 2 ≠ 0 := by linarith
  have hA32sq : (A - 3 / 2) ^ 2 ≠ 0 := pow_ne_zero 2 hA32
  have h2A3 : 2 * A - 3 ≠ 0 := by linarith
  have hA23 : A * 2 - 3 ≠ 0 := by linarith
  have he : 0 < e := by simp only [e]; positivity
  have hscalePlus :
      thetaCuspSingleAtomReflectionScale n (u + t) = A * e := by
    simp only [thetaCuspSingleAtomReflectionScale, A, e]
    rw [show 2 * (u + t) = 2 * u + 2 * t by ring, Real.exp_add]
    ring
  have hscaleMinus :
      thetaCuspSingleAtomReflectionScale n (u - t) = A / e := by
    simp only [thetaCuspSingleAtomReflectionScale, A, e]
    rw [show 2 * (u - t) = 2 * u - 2 * t by ring, Real.exp_sub]
    ring
  have hfive :
      Real.exp (5 * (u + t) / 2) * Real.exp (5 * (u - t) / 2) =
        Real.exp (5 * u / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have heInv : Real.exp (-(2 * t)) = e⁻¹ := by
    simp only [e, Real.exp_neg]
  have hcosh : Real.cosh (2 * t) = (e + e⁻¹) / 2 := by
    rw [Real.cosh_eq, heInv]
  have hpoly :
      (A * e - 3 / 2) * (A / e - 3 / 2) =
        (A - 3 / 2) ^ 2 *
          (1 - thetaCuspSingleAtomReflectionLambda A * z) := by
    have hlambda :
        (A - 3 / 2) ^ 2 * thetaCuspSingleAtomReflectionLambda A =
          3 * A := by
      unfold thetaCuspSingleAtomReflectionLambda
      field_simp [hA32sq, h2A3, hA23]
    have hraw :
        (A * e - 3 / 2) * (A / e - 3 / 2) =
          (A - 3 / 2) ^ 2 - 3 * A * z := by
      simp only [z, thetaCuspSingleAtomReflectionDefect, hcosh]
      field_simp [he.ne']
      ring
    rw [hraw, mul_sub, mul_one]
    rw [show (A - 3 / 2) ^ 2 *
        (thetaCuspSingleAtomReflectionLambda A * z) =
      3 * A * z by rw [← mul_assoc, hlambda]]
  have hgauss :
      Real.exp (-(A * e)) * Real.exp (-(A / e)) =
        Real.exp (-A) ^ 2 * Real.exp (-2 * A * z) := by
    have hexponent :
        -(A * e) + -(A / e) = -A + -A + (-2 * A * z) := by
      simp only [z, thetaCuspSingleAtomReflectionDefect, hcosh]
      field_simp [he.ne']
      ring
    rw [pow_two, ← Real.exp_add, ← Real.exp_add, hexponent, Real.exp_add]
  rw [thetaCuspSourceTerm_eq_singleAtomScale,
    thetaCuspSourceTerm_eq_singleAtomScale,
    thetaCuspSourceTerm_eq_singleAtomScale]
  rw [hscalePlus, hscaleMinus]
  unfold thetaCuspSingleAtomReflectedNormalizedModel
    thetaCuspSingleAtomReflectionFactor
  rw [show thetaCuspSingleAtomReflectionScale n u = A by rfl,
    show thetaCuspSingleAtomReflectionDefect t = z by rfl]
  calc
    _ = (4 * Real.pi * (n : ℝ) ^ 2) ^ 2 *
          (Real.exp (5 * (u + t) / 2) * Real.exp (5 * (u - t) / 2)) *
          ((A * e - 3 / 2) * (A / e - 3 / 2)) *
          (Real.exp (-(A * e)) * Real.exp (-(A / e))) := by ring
    _ = ((4 * Real.pi * (n : ℝ) ^ 2) ^ 2 *
          Real.exp (5 * u / 2) ^ 2 * (A - 3 / 2) ^ 2 *
            Real.exp (-A) ^ 2) *
          ((1 - thetaCuspSingleAtomReflectionLambda A * z) *
            Real.exp (-2 * A * z)) := by
      rw [hfive, hpoly, hgauss]
      ring
    _ = _ := by ring

/-- Exact normalized reflected-product form of one source atom on one modular half-line. -/
theorem thetaCuspSourceTerm_reflected_normalized_eq_singleAtomModel
    {n : ℕ} (hn : 0 < n) {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) n /
        thetaCuspSourceTerm u n ^ 2 =
      thetaCuspSingleAtomReflectedNormalizedModel
        (thetaCuspSingleAtomReflectionScale n u)
        (thetaCuspSingleAtomReflectionDefect t) := by
  have hu : 0 ≤ u := le_trans ht htu
  have huPos : 0 < thetaCuspSourceTerm u n := by
    rw [thetaCuspSourceTerm_eq_singleAtomScale]
    have hscale : 3 / 2 <
        thetaCuspSingleAtomReflectionScale n u := by
      linarith [three_lt_thetaCuspSingleAtomReflectionScale hn hu]
    positivity
  apply (div_eq_iff (pow_ne_zero 2 huPos.ne')).2
  rw [thetaCuspSourceTerm_reflected_mul_eq_singleAtomModel hn ht htu]
  ring

/-- The source atom's exact reflected factor is positive in the same-half-line chamber. -/
theorem thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
    {n : ℕ} (hn : 0 < n) {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    0 < thetaCuspSingleAtomReflectionFactor
      (thetaCuspSingleAtomReflectionScale n u)
      (thetaCuspSingleAtomReflectionDefect t) := by
  have hleft : 0 < thetaCuspSourceTerm (u - t) n := by
    rw [thetaCuspSourceTerm_eq_singleAtomScale]
    have hscale : 3 / 2 <
        thetaCuspSingleAtomReflectionScale n (u - t) := by
      linarith [three_lt_thetaCuspSingleAtomReflectionScale hn (by linarith : 0 ≤ u - t)]
    positivity
  have hright : 0 < thetaCuspSourceTerm (u + t) n := by
    rw [thetaCuspSourceTerm_eq_singleAtomScale]
    have hscale : 3 / 2 <
        thetaCuspSingleAtomReflectionScale n (u + t) := by
      linarith [three_lt_thetaCuspSingleAtomReflectionScale hn (by linarith : 0 ≤ u + t)]
    positivity
  have hcenter : 0 < thetaCuspSourceTerm u n := by
    rw [thetaCuspSourceTerm_eq_singleAtomScale]
    have hscale : 3 / 2 <
        thetaCuspSingleAtomReflectionScale n u := by
      linarith [three_lt_thetaCuspSingleAtomReflectionScale hn (by linarith : 0 ≤ u)]
    positivity
  have hmodel :
      0 < thetaCuspSingleAtomReflectedNormalizedModel
        (thetaCuspSingleAtomReflectionScale n u)
        (thetaCuspSingleAtomReflectionDefect t) := by
    rw [← thetaCuspSourceTerm_reflected_normalized_eq_singleAtomModel hn ht htu]
    positivity
  unfold thetaCuspSingleAtomReflectedNormalizedModel at hmodel
  exact (pos_of_mul_pos_left hmodel (Real.exp_pos _).le)

/-- **Unconditional single-atom source theorem.**  Every positive theta atom has strict reflected
Riccati contraction whenever the two reflected arguments remain on the nonnegative modular
half-line. -/
theorem thetaCuspSourceTerm_reflectedRiccatiMargin_pos
    {n : ℕ} (hn : 0 < n) {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < thetaCuspSingleAtomReflectedRiccatiMargin
      (thetaCuspSingleAtomReflectionScale n u)
      (thetaCuspSingleAtomReflectionDefect t)
      (2 * Real.sinh (2 * t)) := by
  have hu : 0 ≤ u := le_trans ht.le htu
  have hA : 3 < thetaCuspSingleAtomReflectionScale n u := by
    exact three_lt_thetaCuspSingleAtomReflectionScale hn hu
  have hz : 0 ≤ thetaCuspSingleAtomReflectionDefect t := by
    unfold thetaCuspSingleAtomReflectionDefect
    exact sub_nonneg.mpr (Real.one_le_cosh (2 * t))
  have hz' : 0 < 2 * Real.sinh (2 * t) := by
    have hsinh : 0 < Real.sinh (2 * t) := Real.sinh_pos_iff.mpr (by linarith)
    positivity
  exact thetaCuspSingleAtomReflectedRiccatiMargin_pos hA hz hz'
    (thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine hn ht.le htu)

end

end RHTower
