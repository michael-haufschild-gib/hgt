import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A periodic Hessian with a uniform eigenvalue gap

The seed of Lemma 1.1 in Ando–Umehara, arXiv:2610.34036, is
`F(x,y) = a(x) - a(y) + sin x sin y`, where `a(t) = sin⁴ t + 3 sin² t`.
Its trace-free coordinates are `12 - 16(sin⁴ x + sin⁴ y)` and `2 cos x cos y`.
Their squared norm is at least `1/16`: a small cosine forces the real
coordinate below `-1/4`, while two large cosines control the imaginary one.
This gives an explicit spectral separation for planar symmetric tensor fields.
-/

namespace GaloisForLFunctions.HilbertMetric.Geometry.TrigonometricHessian

open Real
noncomputable section

def seedAxis (t : ℝ) : ℝ := sin t ^ 4 + 3 * sin t ^ 2

def seed (x y : ℝ) : ℝ := seedAxis x - seedAxis y + sin x * sin y

def axisSlope (t : ℝ) : ℝ := 4 * sin t ^ 3 * cos t + 6 * sin t * cos t

theorem axis_hasDerivAt (t : ℝ) : HasDerivAt seedAxis (axisSlope t) t := by
  have h := ((hasDerivAt_sin t).pow 4).add (((hasDerivAt_sin t).pow 2).const_mul 3)
  change HasDerivAt seedAxis
    (4 * sin t ^ 3 * cos t + 3 * (2 * sin t ^ 1 * cos t)) t at h
  have he : 4 * sin t ^ 3 * cos t + 3 * (2 * sin t ^ 1 * cos t) = axisSlope t := by
    unfold axisSlope
    ring
  rwa [he] at h

theorem axisSlope_hasDerivAt (t : ℝ) :
    HasDerivAt axisSlope (6 - 16 * sin t ^ 4) t := by
  have h := ((((hasDerivAt_sin t).pow 3).const_mul 4).mul (hasDerivAt_cos t)).add
    (((hasDerivAt_sin t).const_mul 6).mul (hasDerivAt_cos t))
  change HasDerivAt axisSlope
    (4 * (3 * sin t ^ 2 * cos t) * cos t + 4 * sin t ^ 3 * -sin t +
      (6 * cos t * cos t + 6 * sin t * -sin t)) t at h
  have he : 4 * (3 * sin t ^ 2 * cos t) * cos t + 4 * sin t ^ 3 * -sin t +
      (6 * cos t * cos t + 6 * sin t * -sin t) = 6 - 16 * sin t ^ 4 := by
    linear_combination (12 * sin t ^ 2 + 6) * sin_sq_add_cos_sq t
  rwa [he] at h

/-- Exact second derivative of the one-variable seed. -/
theorem axis_second_derivative (t : ℝ) :
    deriv (deriv seedAxis) t = 6 - 16 * sin t ^ 4 := by
  have h : deriv seedAxis = axisSlope := funext fun x => (axis_hasDerivAt x).deriv
  rw [h]
  exact (axisSlope_hasDerivAt t).deriv

theorem seed_x_hasDerivAt (x y : ℝ) :
    HasDerivAt (fun t => seed t y) (axisSlope x + cos x * sin y) x := by
  exact ((axis_hasDerivAt x).sub_const _).add ((hasDerivAt_sin x).mul_const _)

theorem seed_y_hasDerivAt (x y : ℝ) :
    HasDerivAt (seed x) (-axisSlope y + sin x * cos y) y := by
  exact ((axis_hasDerivAt y).const_sub _).add ((hasDerivAt_sin y).const_mul _)

/-- All Hessian entries are obtained from actual derivatives of the seed. -/
theorem seed_hessian (x y : ℝ) :
    deriv (deriv (fun t => seed t y)) x = 6 - 16 * sin x ^ 4 - sin x * sin y ∧
      deriv (deriv (seed x)) y = -(6 - 16 * sin y ^ 4) - sin x * sin y ∧
      deriv (fun t => deriv (fun s => seed s t) x) y = cos x * cos y := by
  have hx : ∀ y, deriv (fun t => seed t y) = fun t => axisSlope t + cos t * sin y :=
    fun y => funext fun x => (seed_x_hasDerivAt x y).deriv
  have hy : deriv (seed x) = fun t => -axisSlope t + sin x * cos t :=
    funext fun y => (seed_y_hasDerivAt x y).deriv
  constructor
  · rw [hx]
    have h := ((axisSlope_hasDerivAt x).fun_add
      ((hasDerivAt_cos x).mul_const (sin y))).deriv
    convert h using 1 <;> ring
  constructor
  · rw [hy]
    have h := ((axisSlope_hasDerivAt y).neg.fun_add
      ((hasDerivAt_cos y).const_mul (sin x))).deriv
    simp only [Pi.neg_apply] at h
    convert h using 1 <;> ring
  · simp only [hx]
    exact (((hasDerivAt_sin y).const_mul (cos x)).const_add (axisSlope x)).deriv

/-- Difference of diagonal Hessian entries. -/
def anisotropy (x y : ℝ) : ℝ := 12 - 16 * (sin x ^ 4 + sin y ^ 4)

/-- Twice the mixed Hessian entry. -/
def shear (x y : ℝ) : ℝ := 2 * cos x * cos y

theorem hessian_coordinates (x y : ℝ) :
    deriv (deriv (fun t => seed t y)) x - deriv (deriv (seed x)) y = anisotropy x y ∧
      2 * deriv (fun t => deriv (fun s => seed s t) x) y = shear x y := by
  obtain ⟨hxx, hyy, hxy⟩ := seed_hessian x y
  rw [hxx, hyy, hxy]
  constructor <;> dsimp [anisotropy, shear] <;> ring

/-- A uniform explicit gap, requiring no compactness or chosen minimizing point. -/
theorem squared_gap_lower_bound (x y : ℝ) :
    (1 / 16 : ℝ) ≤ anisotropy x y ^ 2 + shear x y ^ 2 := by
  have hsmall (u v : ℝ) (hu : cos u ^ 2 ≤ 1 / 8) : anisotropy u v ≤ -(1 / 4) := by
    have ht := sin_sq_add_cos_sq u
    have hs : 7 / 8 ≤ sin u ^ 2 := by linarith only [ht, hu]
    have h4 : (49 / 64 : ℝ) ≤ sin u ^ 4 := by
      nlinarith only [sq_nonneg (sin u ^ 2 - 7 / 8), hs]
    dsimp [anisotropy]
    nlinarith only [h4, sq_nonneg (sin v ^ 2)]
  by_cases hcx : cos x ^ 2 ≤ 1 / 8
  · have ha := hsmall x y hcx
    nlinarith only [ha, sq_nonneg (anisotropy x y + 1 / 4), sq_nonneg (shear x y)]
  by_cases hcy : cos y ^ 2 ≤ 1 / 8
  · have ha := hsmall y x hcy
    rw [anisotropy, add_comm (sin y ^ 4)] at ha
    change anisotropy x y ≤ -(1 / 4) at ha
    nlinarith only [ha, sq_nonneg (anisotropy x y + 1 / 4), sq_nonneg (shear x y)]
  · have hp : (1 / 8 : ℝ) * (1 / 8) ≤ cos x ^ 2 * cos y ^ 2 :=
      mul_le_mul (le_of_lt (lt_of_not_ge hcx)) (le_of_lt (lt_of_not_ge hcy))
        (by norm_num) (sq_nonneg _)
    have he : shear x y ^ 2 = 4 * (cos x ^ 2 * cos y ^ 2) := by
      unfold shear
      ring
    nlinarith only [hp, he, sq_nonneg (anisotropy x y)]

/-- The periodic Hessian is nowhere scalar. -/
theorem hessian_nowhere_scalar (x y : ℝ) :
    ¬ (deriv (deriv (fun t => seed t y)) x = deriv (deriv (seed x)) y ∧
      deriv (fun t => deriv (fun s => seed s t) x) y = 0) := by
  rintro ⟨hdiag, hmix⟩
  have h := hessian_coordinates x y
  have ha : anisotropy x y = 0 := by rw [hdiag, sub_self] at h; exact h.1.symm
  have hs : shear x y = 0 := by rw [hmix, mul_zero] at h; exact h.2.symm
  have hgap := squared_gap_lower_bound x y
  rw [ha, hs] at hgap
  norm_num at hgap

/-- Arbitrary perturbations lose at most their squared trace-free size in this gap bound. -/
theorem perturbed_gap_lower_bound (x y u v : ℝ) :
    (1 / 32 : ℝ) - (u ^ 2 + v ^ 2) ≤
      (anisotropy x y + u) ^ 2 + (shear x y + v) ^ 2 := by
  nlinarith only [squared_gap_lower_bound x y,
    sq_nonneg (anisotropy x y + 2 * u), sq_nonneg (shear x y + 2 * v)]

/-- The stability estimate expressed in the actual three Hessian entries. -/
theorem hessian_perturbation_bound (x y dxx dyy dxy : ℝ) :
    (1 / 32 : ℝ) - ((dxx - dyy) ^ 2 + 4 * dxy ^ 2) ≤
      (deriv (deriv (fun t => seed t y)) x + dxx -
        (deriv (deriv (seed x)) y + dyy)) ^ 2 +
      4 * (deriv (fun t => deriv (fun s => seed s t) x) y + dxy) ^ 2 := by
  obtain ⟨ha, hs⟩ := hessian_coordinates x y
  have h := perturbed_gap_lower_bound x y (dxx - dyy) (2 * dxy)
  rw [← ha, ← hs] at h
  nlinarith only [h]

#print axioms seed_hessian
#print axioms squared_gap_lower_bound
#print axioms hessian_nowhere_scalar
#print axioms hessian_perturbation_bound

end
end GaloisForLFunctions.HilbertMetric.Geometry.TrigonometricHessian
