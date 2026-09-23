import GaloisForLFunctions.HTGeometry.ThresholdDerivativeGlue
import GaloisForLFunctions.RHTower.RapidExponentialFockPotentialGeometry

/-!
# A `C²` rapid exponential Fock potential with a strictly subharmonic head

For `0 < a < 1/2`, an explicit even quartic head is matched in value, slope, and curvature to
`exp (2 a r)` at radius one.  The resulting radial profile is `C²`, positive, has strictly
positive planar radial Laplacian on `r ≥ 0`, and agrees exactly with the rapid exponential model
on the full tail.  Consequently its adapted radius has the required two-sided `exp (-a r)` scale
and vanishes at infinity.  Twice-continuous differentiability is the regularity required by the
Constantin--Peláez rapid radial class.
-/

open Filter Topology

namespace RHTower

noncomputable section

def smoothRapidExponentialFockHeadA (a : ℝ) : ℝ :=
  (4 - 5 * a + 2 * a ^ (2 : ℕ)) / 4

def smoothRapidExponentialFockHeadB (a : ℝ) : ℝ :=
  a * (3 - 2 * a) / 2

def smoothRapidExponentialFockHeadC (a : ℝ) : ℝ :=
  a * (2 * a - 1) / 4

def smoothRapidExponentialFockHeadPolynomial (a : ℝ) : Polynomial ℝ :=
  Polynomial.C (smoothRapidExponentialFockHeadA a) +
    Polynomial.C (smoothRapidExponentialFockHeadB a) * Polynomial.X ^ (2 : ℕ) +
    Polynomial.C (smoothRapidExponentialFockHeadC a) * Polynomial.X ^ (4 : ℕ)

def smoothRapidExponentialFockHeadPotential (a r : ℝ) : ℝ :=
  Real.exp (2 * a) * Polynomial.eval r (smoothRapidExponentialFockHeadPolynomial a)

def smoothRapidExponentialFockHeadSlope (a r : ℝ) : ℝ :=
  Real.exp (2 * a) *
    Polynomial.eval r (Polynomial.derivative (smoothRapidExponentialFockHeadPolynomial a))

def smoothRapidExponentialFockHeadCurvature (a r : ℝ) : ℝ :=
  Real.exp (2 * a) *
    Polynomial.eval r
      (Polynomial.derivative (Polynomial.derivative
        (smoothRapidExponentialFockHeadPolynomial a)))

def smoothRapidExponentialFockHeadLaplacianDensity (a r : ℝ) : ℝ :=
  Real.exp (2 * a) *
    (4 * smoothRapidExponentialFockHeadB a +
      16 * smoothRapidExponentialFockHeadC a * r ^ (2 : ℕ))

def smoothRapidExponentialFockPotential (a r : ℝ) : ℝ :=
  if r < 1 then smoothRapidExponentialFockHeadPotential a r
  else rapidExponentialFockPotential a r

def smoothRapidExponentialFockRadialSlope (a r : ℝ) : ℝ :=
  if r < 1 then smoothRapidExponentialFockHeadSlope a r
  else rapidExponentialFockRadialSlope a r

def smoothRapidExponentialFockRadialCurvature (a r : ℝ) : ℝ :=
  if r < 1 then smoothRapidExponentialFockHeadCurvature a r
  else rapidExponentialFockRadialCurvature a r

def smoothRapidExponentialFockLaplacianDensity (a r : ℝ) : ℝ :=
  if r < 1 then smoothRapidExponentialFockHeadLaplacianDensity a r
  else rapidExponentialFockLaplacianDensity a r

def smoothRapidExponentialFockAdaptedRadius (a r : ℝ) : ℝ :=
  (Real.sqrt (smoothRapidExponentialFockLaplacianDensity a r))⁻¹

theorem smoothRapidExponentialFockHeadPotential_formula (a r : ℝ) :
    smoothRapidExponentialFockHeadPotential a r =
      Real.exp (2 * a) *
        (smoothRapidExponentialFockHeadA a +
          smoothRapidExponentialFockHeadB a * r ^ (2 : ℕ) +
          smoothRapidExponentialFockHeadC a * r ^ (4 : ℕ)) := by
  simp [smoothRapidExponentialFockHeadPotential,
    smoothRapidExponentialFockHeadPolynomial]

theorem smoothRapidExponentialFockHeadSlope_formula (a r : ℝ) :
    smoothRapidExponentialFockHeadSlope a r =
      Real.exp (2 * a) *
        (2 * smoothRapidExponentialFockHeadB a * r +
          4 * smoothRapidExponentialFockHeadC a * r ^ (3 : ℕ)) := by
  simp [smoothRapidExponentialFockHeadSlope,
    smoothRapidExponentialFockHeadPolynomial]
  ring

theorem smoothRapidExponentialFockHeadCurvature_formula (a r : ℝ) :
    smoothRapidExponentialFockHeadCurvature a r =
      Real.exp (2 * a) *
        (2 * smoothRapidExponentialFockHeadB a +
          12 * smoothRapidExponentialFockHeadC a * r ^ (2 : ℕ)) := by
  simp [smoothRapidExponentialFockHeadCurvature,
    smoothRapidExponentialFockHeadPolynomial]
  ring

theorem hasDerivAt_smoothRapidExponentialFockHeadPotential (a r : ℝ) :
    HasDerivAt (smoothRapidExponentialFockHeadPotential a)
      (smoothRapidExponentialFockHeadSlope a r) r := by
  have h := ((smoothRapidExponentialFockHeadPolynomial a).hasDerivAt r).const_mul
    (Real.exp (2 * a))
  rw [hasDerivAt_iff_tendsto_slope] at h ⊢
  rw [show smoothRapidExponentialFockHeadPotential a =
    (fun y : ℝ => Real.exp (2 * a) *
      Polynomial.eval y (smoothRapidExponentialFockHeadPolynomial a)) by rfl]
  simpa [smoothRapidExponentialFockHeadSlope] using h

theorem hasDerivAt_smoothRapidExponentialFockHeadSlope (a r : ℝ) :
    HasDerivAt (smoothRapidExponentialFockHeadSlope a)
      (smoothRapidExponentialFockHeadCurvature a r) r := by
  have h := ((Polynomial.derivative
    (smoothRapidExponentialFockHeadPolynomial a)).hasDerivAt r).const_mul
      (Real.exp (2 * a))
  rw [hasDerivAt_iff_tendsto_slope] at h ⊢
  rw [show smoothRapidExponentialFockHeadSlope a =
    (fun y : ℝ => Real.exp (2 * a) *
      Polynomial.eval y (Polynomial.derivative
        (smoothRapidExponentialFockHeadPolynomial a))) by rfl]
  simpa [smoothRapidExponentialFockHeadCurvature] using h

theorem smoothRapidExponentialFockHeadPotential_one (a : ℝ) :
    smoothRapidExponentialFockHeadPotential a 1 =
      rapidExponentialFockPotential a 1 := by
  rw [smoothRapidExponentialFockHeadPotential_formula]
  unfold smoothRapidExponentialFockHeadA
    smoothRapidExponentialFockHeadB smoothRapidExponentialFockHeadC
    rapidExponentialFockPotential
  ring

theorem smoothRapidExponentialFockHeadSlope_one (a : ℝ) :
    smoothRapidExponentialFockHeadSlope a 1 =
      rapidExponentialFockRadialSlope a 1 := by
  rw [smoothRapidExponentialFockHeadSlope_formula]
  unfold smoothRapidExponentialFockHeadB
    smoothRapidExponentialFockHeadC rapidExponentialFockRadialSlope
  ring

theorem smoothRapidExponentialFockHeadCurvature_one (a : ℝ) :
    smoothRapidExponentialFockHeadCurvature a 1 =
      rapidExponentialFockRadialCurvature a 1 := by
  rw [smoothRapidExponentialFockHeadCurvature_formula]
  unfold smoothRapidExponentialFockHeadB
    smoothRapidExponentialFockHeadC rapidExponentialFockRadialCurvature
  ring

theorem hasDerivAt_smoothRapidExponentialFockPotential (a r : ℝ) :
    HasDerivAt (smoothRapidExponentialFockPotential a)
      (smoothRapidExponentialFockRadialSlope a r) r := by
  exact HTGeometry.hasDerivAt_ite_lt
    (fun x => hasDerivAt_smoothRapidExponentialFockHeadPotential a x)
    (fun x => hasDerivAt_rapidExponentialFockPotential a x)
    (smoothRapidExponentialFockHeadPotential_one a)
    (smoothRapidExponentialFockHeadSlope_one a)

theorem hasDerivAt_smoothRapidExponentialFockRadialSlope (a r : ℝ) :
    HasDerivAt (smoothRapidExponentialFockRadialSlope a)
      (smoothRapidExponentialFockRadialCurvature a r) r := by
  exact HTGeometry.hasDerivAt_ite_lt
    (fun x => hasDerivAt_smoothRapidExponentialFockHeadSlope a x)
    (fun x => hasDerivAt_rapidExponentialFockRadialSlope a x)
    (smoothRapidExponentialFockHeadSlope_one a)
    (smoothRapidExponentialFockHeadCurvature_one a)

theorem continuous_smoothRapidExponentialFockRadialCurvature (a : ℝ) :
    Continuous (smoothRapidExponentialFockRadialCurvature a) := by
  apply HTGeometry.continuous_ite_lt
  · unfold smoothRapidExponentialFockHeadCurvature
    fun_prop
  · unfold rapidExponentialFockRadialCurvature
    fun_prop
  · exact smoothRapidExponentialFockHeadCurvature_one a

theorem contDiff_two_smoothRapidExponentialFockPotential (a : ℝ) :
    ContDiff ℝ 2 (smoothRapidExponentialFockPotential a) := by
  apply HTGeometry.contDiff_succ_of_hasDerivAt
    (fun r => hasDerivAt_smoothRapidExponentialFockPotential a r)
  apply HTGeometry.contDiff_succ_of_hasDerivAt
    (fun r => hasDerivAt_smoothRapidExponentialFockRadialSlope a r)
  exact contDiff_zero.mpr (continuous_smoothRapidExponentialFockRadialCurvature a)

theorem smoothRapidExponentialFockPotential_eq_tail
    {a r : ℝ} (hr : 1 ≤ r) :
    smoothRapidExponentialFockPotential a r = rapidExponentialFockPotential a r := by
  simp [smoothRapidExponentialFockPotential, not_lt.mpr hr]

theorem smoothRapidExponentialFockHeadPotential_pos
    {a r : ℝ} (ha : 0 < a) (haHalf : a < 1 / 2) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 < smoothRapidExponentialFockHeadPotential a r := by
  have hrSq : r ^ (2 : ℕ) ≤ 1 := by nlinarith [sq_nonneg r]
  have hC : smoothRapidExponentialFockHeadC a < 0 := by
    unfold smoothRapidExponentialFockHeadC
    have hlin : 2 * a - 1 < 0 := by linarith
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha hlin) (by norm_num)
  have hA : 0 < smoothRapidExponentialFockHeadA a := by
    unfold smoothRapidExponentialFockHeadA
    have : 0 < 4 - 5 * a + 2 * a ^ (2 : ℕ) := by nlinarith [sq_nonneg (a - 1)]
    positivity
  have hBC : 0 < smoothRapidExponentialFockHeadB a +
      smoothRapidExponentialFockHeadC a := by
    unfold smoothRapidExponentialFockHeadB smoothRapidExponentialFockHeadC
    nlinarith
  have hBCr : 0 < smoothRapidExponentialFockHeadB a +
      smoothRapidExponentialFockHeadC a * r ^ (2 : ℕ) := by
    nlinarith
  rw [smoothRapidExponentialFockHeadPotential_formula]
  have hbracket : 0 < smoothRapidExponentialFockHeadA a +
      smoothRapidExponentialFockHeadB a * r ^ (2 : ℕ) +
      smoothRapidExponentialFockHeadC a * r ^ (4 : ℕ) := by
    have hrSq0 : 0 ≤ r ^ (2 : ℕ) := sq_nonneg r
    have : 0 ≤ r ^ (2 : ℕ) *
        (smoothRapidExponentialFockHeadB a +
          smoothRapidExponentialFockHeadC a * r ^ (2 : ℕ)) :=
      mul_nonneg hrSq0 hBCr.le
    nlinarith
  exact mul_pos (Real.exp_pos _) hbracket

theorem smoothRapidExponentialFockPotential_pos
    {a r : ℝ} (ha : 0 < a) (haHalf : a < 1 / 2) (hr : 0 ≤ r) :
    0 < smoothRapidExponentialFockPotential a r := by
  by_cases hr1 : r < 1
  · simp only [smoothRapidExponentialFockPotential, if_pos hr1]
    exact smoothRapidExponentialFockHeadPotential_pos ha haHalf hr hr1.le
  · simp only [smoothRapidExponentialFockPotential, if_neg hr1,
      rapidExponentialFockPotential]
    positivity

theorem smoothRapidExponentialFockLaplacianDensity_eq_tail
    {a r : ℝ} (hr : 1 ≤ r) :
    smoothRapidExponentialFockLaplacianDensity a r =
      rapidExponentialFockLaplacianDensity a r := by
  simp [smoothRapidExponentialFockLaplacianDensity, not_lt.mpr hr]

theorem smoothRapidExponentialFockHeadLaplacianDensity_pos
    {a r : ℝ} (ha : 0 < a) (haHalf : a < 1 / 2) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 < smoothRapidExponentialFockHeadLaplacianDensity a r := by
  have hrSq : r ^ (2 : ℕ) ≤ 1 := by nlinarith [sq_nonneg r]
  have hC : smoothRapidExponentialFockHeadC a < 0 := by
    unfold smoothRapidExponentialFockHeadC
    have : 2 * a - 1 < 0 := by linarith
    have hprod : a * (2 * a - 1) < 0 := mul_neg_of_pos_of_neg ha this
    exact div_neg_of_neg_of_pos hprod (by norm_num)
  have hmin :
      4 * smoothRapidExponentialFockHeadB a +
          16 * smoothRapidExponentialFockHeadC a ≤
        4 * smoothRapidExponentialFockHeadB a +
          16 * smoothRapidExponentialFockHeadC a * r ^ (2 : ℕ) := by
    nlinarith
  have hatOne :
      0 < 4 * smoothRapidExponentialFockHeadB a +
          16 * smoothRapidExponentialFockHeadC a := by
    unfold smoothRapidExponentialFockHeadB smoothRapidExponentialFockHeadC
    nlinarith
  unfold smoothRapidExponentialFockHeadLaplacianDensity
  exact mul_pos (Real.exp_pos _) (hatOne.trans_le hmin)

theorem smoothRapidExponentialFockLaplacianDensity_pos
    {a r : ℝ} (ha : 0 < a) (haHalf : a < 1 / 2) (hr : 0 ≤ r) :
    0 < smoothRapidExponentialFockLaplacianDensity a r := by
  by_cases hr1 : r < 1
  · simp only [smoothRapidExponentialFockLaplacianDensity, if_pos hr1]
    exact smoothRapidExponentialFockHeadLaplacianDensity_pos ha haHalf hr hr1.le
  · simp only [smoothRapidExponentialFockLaplacianDensity, if_neg hr1]
    exact rapidExponentialFockLaplacianDensity_pos ha (lt_of_lt_of_le zero_lt_one (not_lt.mp hr1))

theorem smoothRapidExponentialFockAdaptedRadius_pos
    {a r : ℝ} (ha : 0 < a) (haHalf : a < 1 / 2) (hr : 0 ≤ r) :
    0 < smoothRapidExponentialFockAdaptedRadius a r := by
  unfold smoothRapidExponentialFockAdaptedRadius
  exact inv_pos.mpr (Real.sqrt_pos.2
    (smoothRapidExponentialFockLaplacianDensity_pos ha haHalf hr))

theorem smoothRapidExponentialFockAdaptedRadius_eq_tail
    {a r : ℝ} (hr : 1 ≤ r) :
    smoothRapidExponentialFockAdaptedRadius a r =
      rapidExponentialFockAdaptedRadius a r := by
  simp [smoothRapidExponentialFockAdaptedRadius,
    rapidExponentialFockAdaptedRadius,
    smoothRapidExponentialFockLaplacianDensity_eq_tail hr]

theorem smoothRapidExponentialFockAdaptedRadius_upper
    {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) :
    smoothRapidExponentialFockAdaptedRadius a r ≤
      (2 * a)⁻¹ * Real.exp (-a * r) := by
  rw [smoothRapidExponentialFockAdaptedRadius_eq_tail hr]
  exact rapidExponentialFockAdaptedRadius_upper ha (zero_lt_one.trans_le hr)

theorem smoothRapidExponentialFockAdaptedRadius_lower
    {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) :
    (Real.sqrt (4 * a ^ (2 : ℕ) + 2 * a))⁻¹ * Real.exp (-a * r) ≤
      smoothRapidExponentialFockAdaptedRadius a r := by
  rw [smoothRapidExponentialFockAdaptedRadius_eq_tail hr]
  exact rapidExponentialFockAdaptedRadius_lower ha hr

theorem tendsto_smoothRapidExponentialFockAdaptedRadius_atTop
    {a : ℝ} (ha : 0 < a) :
    Tendsto (smoothRapidExponentialFockAdaptedRadius a) atTop (nhds 0) := by
  apply (tendsto_congr' ?_).mpr (tendsto_rapidExponentialFockAdaptedRadius_atTop ha)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  exact smoothRapidExponentialFockAdaptedRadius_eq_tail hr

theorem smoothRapidExponentialFockLaplacianDensity_eq
    {a r : ℝ} (hr : 0 < r) :
    smoothRapidExponentialFockRadialCurvature a r +
        smoothRapidExponentialFockRadialSlope a r / r =
      smoothRapidExponentialFockLaplacianDensity a r := by
  by_cases hr1 : r < 1
  · simp only [smoothRapidExponentialFockRadialCurvature,
      smoothRapidExponentialFockRadialSlope,
      smoothRapidExponentialFockLaplacianDensity, if_pos hr1]
    rw [smoothRapidExponentialFockHeadCurvature_formula,
      smoothRapidExponentialFockHeadSlope_formula]
    unfold smoothRapidExponentialFockHeadLaplacianDensity
    field_simp [hr.ne']
    ring
  · simp only [smoothRapidExponentialFockRadialCurvature,
      smoothRapidExponentialFockRadialSlope,
      smoothRapidExponentialFockLaplacianDensity, if_neg hr1]
    exact rapidExponentialFockLaplacianDensity_eq a r hr.ne'

end

end RHTower
