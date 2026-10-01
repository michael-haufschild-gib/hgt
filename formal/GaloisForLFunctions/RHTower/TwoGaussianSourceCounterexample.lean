import GaloisForLFunctions.HTGeometry.PositiveDensityQuantile
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Convex.Deriv

/-!
# The literal positive two-Gaussian Fourier counterexample

The density is `exp (-x²) + exp (-2x²)`. Its actual logarithm is strictly
concave, while its entire literal Fourier integral has a non-real zero.
These facts require no finite-kernel-energy or spectral-reality premise.
-/

open MeasureTheory Set Complex

namespace RHTower.TwoGaussianComparison

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The exact two-Gaussian density cited by the theta history card. -/
def density (x : ℝ) : ℝ := Real.exp (-x ^ 2) + Real.exp (-2 * x ^ 2)

theorem density_pos (x : ℝ) : 0 < density x := by
  unfold density
  positivity

theorem continuous_density : Continuous density := by
  unfold density
  fun_prop

theorem density_neg (x : ℝ) : density (-x) = density x := by
  simp [density]

theorem integrable_density : Integrable density := by
  have h₁ := integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have h₂ := integrable_exp_neg_mul_sq (b := 2) (by norm_num)
  apply (h₁.add h₂).congr
  exact Filter.Eventually.of_forall fun x => by
    simp [density, Pi.add_apply]

/-- A genuine positive source, with the literal density and actual measure. -/
def source : PositiveDensitySource where
  k := density
  continuous_k := continuous_density
  pos_k := density_pos
  integrable_k := integrable_density

theorem source_mass : source.mass = Real.sqrt Real.pi + Real.sqrt (Real.pi / 2) := by
  change (∫ x : ℝ, density x) = _
  change (∫ x : ℝ, Real.exp (-x ^ 2) + Real.exp (-2 * x ^ 2)) = _
  rw [integral_add]
  · simpa using congrArg₂ (· + ·) (integral_gaussian 1) (integral_gaussian 2)
  · simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  · exact integrable_exp_neg_mul_sq (b := 2) (by norm_num)

private def first (x : ℝ) : ℝ :=
  (-2 * x) * Real.exp (-x ^ 2) + (-4 * x) * Real.exp (-2 * x ^ 2)

private def second (x : ℝ) : ℝ :=
  (4 * x ^ 2 - 2) * Real.exp (-x ^ 2) +
    (16 * x ^ 2 - 4) * Real.exp (-2 * x ^ 2)

private theorem gaussian_one_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2))
      ((-2 * x) * Real.exp (-x ^ 2)) x := by
  apply (((hasDerivAt_id x).pow 2).neg).exp.congr_deriv
  simp only [Pi.pow_apply, Pi.neg_apply, id_eq]
  ring

private theorem gaussian_two_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-2 * y ^ 2))
      ((-4 * x) * Real.exp (-2 * x ^ 2)) x := by
  apply (((hasDerivAt_id x).pow 2).const_mul (-2)).exp.congr_deriv
  simp only [Pi.pow_apply, id_eq]
  ring

private theorem density_hasDerivAt (x : ℝ) : HasDerivAt density (first x) x :=
  (gaussian_one_hasDerivAt x).add (gaussian_two_hasDerivAt x)

private theorem first_hasDerivAt (x : ℝ) : HasDerivAt first (second x) x := by
  have h₁ := ((hasDerivAt_id x).const_mul (-2)).mul (gaussian_one_hasDerivAt x)
  have h₂ := ((hasDerivAt_id x).const_mul (-4)).mul (gaussian_two_hasDerivAt x)
  apply (h₁.add h₂).congr_deriv
  simp only [second, id_eq]
  ring

private theorem curvature_pos (x : ℝ) : 0 < first x ^ 2 - density x * second x := by
  let u : ℝ := x ^ 2
  let g : ℝ := Real.exp (-u)
  have hu : 0 ≤ u := sq_nonneg x
  have hg : 0 < g := Real.exp_pos _
  have hh := Real.add_one_le_exp (u / 2)
  have hp := Real.exp_pos (u / 2)
  have hexp : Real.exp u = Real.exp (u / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hbound : 2 * u ≤ Real.exp u := by
    rw [hexp]
    nlinarith [sq_nonneg (u / 2 - 1)]
  have hcancel : Real.exp u * g = 1 := by
    dsimp [g]
    rw [← Real.exp_add]
    simp
  have hprod : 2 * u * g ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hbound hg.le
    rwa [hcancel] at h
  have hbracket : 0 < 1 + (3 - 2 * u) * g + 2 * g ^ 2 := by
    nlinarith [sq_nonneg g]
  have h₂ : Real.exp (-2 * x ^ 2) = g ^ 2 := by
    change Real.exp (-2 * x ^ 2) = Real.exp (-x ^ 2) ^ 2
    rw [pow_two (Real.exp (-x ^ 2)), ← Real.exp_add]
    congr 1
    ring
  have hid : first x ^ 2 - density x * second x =
      2 * g ^ 2 * (1 + (3 - 2 * u) * g + 2 * g ^ 2) := by
    dsimp [first, density, second, u]
    rw [h₂]
    change ((-2 * x) * g + (-4 * x) * g ^ 2) ^ 2 -
      (g + g ^ 2) * ((4 * x ^ 2 - 2) * g + (16 * x ^ 2 - 4) * g ^ 2) = _
    ring
  rw [hid]
  positivity

private theorem deriv_log_density (x : ℝ) :
    deriv (fun y => Real.log (density y)) x = first x / density x :=
  ((density_hasDerivAt x).log (density_pos x).ne').deriv

private theorem deriv_log_density_two (x : ℝ) :
    deriv (deriv (fun y => Real.log (density y))) x =
      (density x * second x - first x ^ 2) / density x ^ 2 := by
  have hfirst : deriv (fun y => Real.log (density y)) =
      fun y => first y / density y := funext deriv_log_density
  rw [hfirst]
  calc
    deriv (fun y => first y / density y) x =
        (second x * density x - first x * first x) / density x ^ 2 :=
      ((first_hasDerivAt x).div (density_hasDerivAt x) (density_pos x).ne').deriv
    _ = _ := by ring

theorem deriv_log_density_two_neg (x : ℝ) :
    deriv (deriv (fun y => Real.log (density y))) x < 0 := by
  rw [deriv_log_density_two]
  exact div_neg_of_neg_of_pos (by linarith [curvature_pos x])
    (pow_pos (density_pos x) 2)

/-- Strict log-concavity is a theorem of the actual literal logarithm. -/
theorem strictConcaveOn_log_density :
    StrictConcaveOn ℝ univ (fun x => Real.log (density x)) := by
  apply strictConcaveOn_univ_of_deriv2_neg
    (continuous_density.log fun x => (density_pos x).ne')
  intro x
  simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
    deriv_log_density_two_neg x

private theorem gaussian_integrand (b : ℝ) (z : ℂ) (x : ℝ) :
    Complex.exp (I * z * x) * (Real.exp (-b * x ^ 2) : ℂ) =
      Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2 + (I * z) * x + 0) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem integrable_fourierGaussian {b : ℝ} (hb : 0 < b) (z : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (I * z * x) *
      (Real.exp (-b * x ^ 2) : ℂ)) := by
  have h := integrable_cexp_quadratic (b := (b : ℂ)) (by simpa using hb) (I * z) 0
  exact h.congr (Filter.Eventually.of_forall fun x => (gaussian_integrand b z x).symm)

private theorem fourierGaussian_integral {b : ℝ} (hb : 0 < b) (z : ℂ) :
    (∫ x : ℝ, Complex.exp (I * z * x) * (Real.exp (-b * x ^ 2) : ℂ)) =
      (Real.sqrt (Real.pi / b) : ℂ) * Complex.exp (-z ^ 2 / (4 * (b : ℂ))) := by
  have h := integral_cexp_quadratic (b := -(b : ℂ)) (by simpa using hb) (I * z) 0
  have hexponent : (0 : ℂ) - (I * z) ^ 2 / (4 * -(b : ℂ)) =
      -z ^ 2 / (4 * (b : ℂ)) := by
    rw [mul_pow, Complex.I_sq]
    simp
    ring
  have hpower : ((Real.pi : ℂ) / (b : ℂ)) ^ (1 / 2 : ℂ) =
      (Real.sqrt (Real.pi / b) : ℂ) := by
    rw [← Complex.ofReal_div, Real.sqrt_eq_rpow]
    convert (Complex.ofReal_cpow (div_pos Real.pi_pos hb).le (1 / 2 : ℝ)).symm
      using 1
    norm_num
  rw [neg_neg, hexponent, hpower] at h
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (gaussian_integrand b z)

/-- The physical complex-frequency transform of the literal source. -/
def transform (z : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (I * z * x) * (source.k x : ℂ)

/-- The entire closed formula with its exact Gaussian mass constants. -/
def closedForm (z : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * Complex.exp (-z ^ 2 / 4) +
    (Real.sqrt (Real.pi / 2) : ℂ) * Complex.exp (-z ^ 2 / 8)

theorem integrable_transform (z : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (I * z * x) * (source.k x : ℂ)) := by
  have h₁ := integrable_fourierGaussian (b := 1) (by norm_num) z
  have h₂ := integrable_fourierGaussian (b := 2) (by norm_num) z
  apply (h₁.add h₂).congr
  exact Filter.Eventually.of_forall fun x => by
    simp [source, density, mul_add, Pi.add_apply]

/-- Exact literal Fourier integration at every complex frequency. -/
theorem transform_eq (z : ℂ) : transform z = closedForm z := by
  unfold transform closedForm
  change (∫ x : ℝ, Complex.exp (I * z * x) * (density x : ℂ)) = _
  simp only [density, Complex.ofReal_add, mul_add]
  rw [integral_add]
  · simpa [show (4 : ℂ) * 2 = 8 by norm_num] using congrArg₂ (· + ·)
      (fourierGaussian_integral (b := 1) (by norm_num) z)
      (fourierGaussian_integral (b := 2) (by norm_num) z)
  · simpa using integrable_fourierGaussian (b := 1) (by norm_num) z
  · exact integrable_fourierGaussian (b := 2) (by norm_num) z

theorem differentiable_transform : Differentiable ℂ transform := by
  have heq : transform = closedForm := funext transform_eq
  rw [heq]
  unfold closedForm
  fun_prop

/-- The actual transform is strictly positive on the whole real line. -/
theorem transform_real_re_pos (t : ℝ) : 0 < (transform (t : ℂ)).re := by
  rw [transform_eq]
  have h₁ : -(t : ℂ) ^ 2 / 4 = ((-t ^ 2 / 4 : ℝ) : ℂ) := by
    push_cast
    rfl
  have h₂ : -(t : ℂ) ^ 2 / 8 = ((-t ^ 2 / 8 : ℝ) : ℂ) := by
    push_cast
    rfl
  simp only [closedForm, h₁, h₂, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_re]
  have hA : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hB : 0 < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.mpr (by positivity)
  positivity

theorem transform_real_ne_zero (t : ℝ) : transform (t : ℂ) ≠ 0 := by
  intro h
  have hp := transform_real_re_pos t
  rw [h] at hp
  norm_num at hp

/-- The square of a constructed non-real zero, using only the exact mass ratio. -/
def zeroSquare : ℂ :=
  -8 * ((Real.log (Real.sqrt (Real.pi / 2) / Real.sqrt Real.pi) : ℂ) +
    (Real.pi : ℂ) * I)

/-- An explicit principal half-power of the source-derived square. -/
def offRealZero : ℂ := zeroSquare ^ (1 / 2 : ℂ)

theorem offRealZero_sq : offRealZero ^ 2 = zeroSquare := by
  unfold offRealZero
  rw [← Complex.cpow_mul_nat]
  norm_num

theorem offRealZero_im_ne_zero : offRealZero.im ≠ 0 := by
  intro hz
  have h := congrArg Complex.im offRealZero_sq
  have hsquare : zeroSquare.im = -8 * Real.pi := by
    simp [zeroSquare, Complex.mul_im]
  rw [hsquare, pow_two, Complex.mul_im, hz] at h
  simp only [mul_zero, zero_mul, add_zero] at h
  linarith [Real.pi_pos]

private theorem exp_offRealZero :
    Complex.exp (-offRealZero ^ 2 / 8) =
      -((Real.sqrt (Real.pi / 2) / Real.sqrt Real.pi : ℝ) : ℂ) := by
  rw [offRealZero_sq]
  have harg : -zeroSquare / 8 =
      (Real.log (Real.sqrt (Real.pi / 2) / Real.sqrt Real.pi) : ℂ) +
        (Real.pi : ℂ) * I := by
    unfold zeroSquare
    ring
  rw [harg, Complex.exp_add_pi_mul_I, ← Complex.ofReal_exp]
  rw [Real.exp_log (div_pos (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_pos.mpr Real.pi_pos))]

/-- The constructed non-real point is a zero of the actual Lebesgue integral. -/
theorem transform_offRealZero : transform offRealZero = 0 := by
  have hd : Complex.exp (-offRealZero ^ 2 / 4) =
      Complex.exp (-offRealZero ^ 2 / 8) ^ 2 := by
    rw [pow_two (Complex.exp (-offRealZero ^ 2 / 8)), ← Complex.exp_add]
    congr 1
    ring
  rw [transform_eq]
  unfold closedForm
  rw [hd, exp_offRealZero]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne']
  ring

/-- Positive even strict log-concavity coexists with a literal off-real Fourier zero. -/
theorem source_counterexample :
    (∀ x : ℝ, source.k (-x) = source.k x) ∧
      StrictConcaveOn ℝ univ (fun x => Real.log (source.k x)) ∧
      (∀ t : ℝ, (transform (t : ℂ)).re > 0) ∧
      ∃ z : ℂ, z.im ≠ 0 ∧ transform z = 0 :=
  ⟨density_neg, strictConcaveOn_log_density, transform_real_re_pos,
    offRealZero, offRealZero_im_ne_zero, transform_offRealZero⟩

end
end RHTower.TwoGaussianComparison
