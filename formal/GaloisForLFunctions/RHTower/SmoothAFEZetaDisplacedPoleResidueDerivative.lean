import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDirectDerivativeTruncation

/-!
# Height derivative of the displaced Gaussian pole residue

The secondary AFE residue is an elementary holomorphic term.  This module
records its exact height derivative on every displaced Levinson line.
-/

noncomputable section

namespace RHTower

open Complex

def smoothAFEZetaDisplacedPoleCoordinate (d τ : ℝ) : ℂ :=
  1 - displacedLinePt d τ

def smoothAFEZetaDisplacedPoleResidueHeightDerivative
    (d x τ : ℝ) : ℂ :=
  let z := smoothAFEZetaDisplacedPoleCoordinate d τ
  let A := (x : ℂ) ^ z
  let E := Complex.exp (z ^ 2)
  let Az := (A * Complex.log (x : ℂ)) * (-I)
  let Ez := E * (2 * z * (-I))
  ((Az * E + A * Ez) * z - (A * E) * (-I)) / z ^ 2

theorem smoothAFEZetaDisplacedPoleCoordinate_ne_zero
    {d : ℝ} (hd : 0 < d) (τ : ℝ) :
    smoothAFEZetaDisplacedPoleCoordinate d τ ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  simp [smoothAFEZetaDisplacedPoleCoordinate, displacedLinePt] at hre
  linarith

theorem hasDerivAt_smoothAFEZetaShiftedPoleResidue_displaced
    {d x : ℝ} (hd : 0 < d) (hx : 0 < x) (τ : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        smoothAFEZetaShiftedPoleResidue (displacedLinePt d u) x)
      (smoothAFEZetaDisplacedPoleResidueHeightDerivative d x τ) τ := by
  let z : ℝ → ℂ := fun u => smoothAFEZetaDisplacedPoleCoordinate d u
  have hz : HasDerivAt z (-I) τ := by
    change HasDerivAt (fun u : ℝ => 1 - displacedLinePt d u) (-I) τ
    simpa only [zero_sub] using
      (hasDerivAt_displacedLinePt d τ).const_sub (1 : ℂ)
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpowC :=
    (Complex.hasStrictDerivAt_const_cpow
      (x := (x : ℂ)) (y := z τ) (Or.inl hxC)).hasDerivAt
  have hpow := hpowC.comp τ hz
  have hexp := (hz.pow 2).cexp
  have hnum := hpow.mul hexp
  have hdiv := hnum.div hz
    (smoothAFEZetaDisplacedPoleCoordinate_ne_zero hd τ)
  have hfun :
      (fun u : ℝ =>
        smoothAFEZetaShiftedPoleResidue (displacedLinePt d u) x) =
      (((fun y : ℂ => (x : ℂ) ^ y) ∘ z) *
        (fun u : ℝ => Complex.exp ((z ^ 2) u))) / z := by
    funext u
    simp only [smoothAFEZetaShiftedPoleResidue, z,
      smoothAFEZetaDisplacedPoleCoordinate, Function.comp_apply, Pi.mul_apply,
      Pi.div_apply, Pi.pow_apply]
  have hcoeff :
      smoothAFEZetaDisplacedPoleResidueHeightDerivative d x τ =
        (((((x : ℂ) ^ z τ * Complex.log (x : ℂ)) * (-I)) *
              Complex.exp ((z ^ 2) τ) +
            (((fun y : ℂ => (x : ℂ) ^ y) ∘ z) τ) *
              (Complex.exp ((z ^ 2) τ) *
                ((2 : ℂ) * (z τ) ^ (2 - 1) * (-I)))) * z τ -
          ((((fun y : ℂ => (x : ℂ) ^ y) ∘ z) *
            (fun u : ℝ => Complex.exp ((z ^ 2) u))) τ) * (-I)) /
            (z τ) ^ 2 := by
    dsimp only [smoothAFEZetaDisplacedPoleResidueHeightDerivative, z,
      Function.comp_apply, Pi.mul_apply, Pi.pow_apply]
    norm_num
  rw [hfun, hcoeff]
  exact hdiv

theorem norm_smoothAFEZetaDisplacedPoleCoordinate_exp_sq
    (d τ : ℝ) :
    ‖Complex.exp ((smoothAFEZetaDisplacedPoleCoordinate d τ) ^ 2)‖ =
      Real.exp ((1 / 2 + d) ^ 2 - τ ^ 2) := by
  rw [Complex.norm_exp]
  have hz : smoothAFEZetaDisplacedPoleCoordinate d τ =
      (((1 / 2 + d : ℝ) : ℂ) - (τ : ℂ) * I) := by
    unfold smoothAFEZetaDisplacedPoleCoordinate displacedLinePt
    push_cast
    ring
  rw [hz]
  simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, sub_self]
  ring_nf

theorem abs_le_norm_smoothAFEZetaDisplacedPoleCoordinate
    (d τ : ℝ) :
    |τ| ≤ ‖smoothAFEZetaDisplacedPoleCoordinate d τ‖ := by
  calc
    |τ| = |(smoothAFEZetaDisplacedPoleCoordinate d τ).im| := by
      simp [smoothAFEZetaDisplacedPoleCoordinate, displacedLinePt]
    _ ≤ ‖smoothAFEZetaDisplacedPoleCoordinate d τ‖ :=
      Complex.abs_im_le_norm _

theorem norm_smoothAFEZetaDisplacedPoleResidueHeightDerivative_le
    {d x τ : ℝ} (hd : 0 < d) (hx : 0 < x) (hτ : 1 ≤ |τ|) :
    ‖smoothAFEZetaDisplacedPoleResidueHeightDerivative d x τ‖ ≤
      x ^ (1 / 2 + d) * Real.exp ((1 / 2 + d) ^ 2) *
        (|Real.log x| + 3) * Real.exp (-(τ ^ 2)) := by
  let z : ℂ := smoothAFEZetaDisplacedPoleCoordinate d τ
  let A : ℂ := (x : ℂ) ^ z
  let E : ℂ := Complex.exp (z ^ 2)
  let Az : ℂ := (A * Complex.log (x : ℂ)) * (-I)
  let Ez : ℂ := E * (2 * z * (-I))
  have hz0 : z ≠ 0 := smoothAFEZetaDisplacedPoleCoordinate_ne_zero hd τ
  have hzone : 1 ≤ ‖z‖ :=
    hτ.trans (abs_le_norm_smoothAFEZetaDisplacedPoleCoordinate d τ)
  have hznorm0 : 0 < ‖z‖ := zero_lt_one.trans_le hzone
  have hA : ‖A‖ = x ^ (1 / 2 + d) := by
    dsimp only [A, z]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 1
    simp [smoothAFEZetaDisplacedPoleCoordinate, displacedLinePt]
    ring_nf
  have hE : ‖E‖ = Real.exp ((1 / 2 + d) ^ 2) * Real.exp (-(τ ^ 2)) := by
    dsimp only [E, z]
    rw [norm_smoothAFEZetaDisplacedPoleCoordinate_exp_sq]
    rw [show (1 / 2 + d) ^ 2 - τ ^ 2 =
        (1 / 2 + d) ^ 2 + (-(τ ^ 2)) by ring, Real.exp_add]
  have hlog : ‖Complex.log (x : ℂ)‖ = |Real.log x| := by
    rw [← Complex.ofReal_log hx.le, Complex.norm_real, Real.norm_eq_abs]
  have hdecomp :
      smoothAFEZetaDisplacedPoleResidueHeightDerivative d x τ =
        Az * E / z + A * E * (2 * (-I)) - A * E * (-I) / z ^ 2 := by
    change ((Az * E + A * Ez) * z - (A * E) * (-I)) / z ^ 2 = _
    rw [show Ez = E * (2 * z * (-I)) by rfl]
    field_simp [hz0]
  rw [hdecomp]
  have hfirst : ‖Az * E / z‖ ≤ ‖A‖ * |Real.log x| * ‖E‖ := by
    rw [norm_div, norm_mul]
    have hAz : ‖Az‖ = ‖A‖ * |Real.log x| := by
      dsimp only [Az]
      rw [norm_mul, norm_mul, norm_neg, norm_I, mul_one, hlog]
    rw [hAz]
    exact (div_le_iff₀ hznorm0).2
      (le_mul_of_one_le_right (by positivity) hzone)
  have hmiddle : ‖A * E * (2 * (-I))‖ = 2 * ‖A‖ * ‖E‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_I]
    norm_num
    ring
  have hlast : ‖A * E * (-I) / z ^ 2‖ ≤ ‖A‖ * ‖E‖ := by
    rw [norm_div, norm_mul, norm_mul, norm_neg, norm_I, mul_one, norm_pow]
    have hzsq : 1 ≤ ‖z‖ ^ 2 := one_le_pow₀ hzone
    exact (div_le_iff₀ (pow_pos hznorm0 2)).2
      (le_mul_of_one_le_right (by positivity) hzsq)
  calc
    ‖Az * E / z + A * E * (2 * -I) - A * E * -I / z ^ 2‖
        ≤ ‖Az * E / z‖ + ‖A * E * (2 * -I)‖ +
            ‖A * E * -I / z ^ 2‖ := by
          exact (norm_sub_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖A‖ * |Real.log x| * ‖E‖) +
          (2 * ‖A‖ * ‖E‖) + (‖A‖ * ‖E‖) := by
      exact add_le_add (add_le_add hfirst hmiddle.le) hlast
    _ = ‖A‖ * ‖E‖ * (|Real.log x| + 3) := by ring
    _ = x ^ (1 / 2 + d) * Real.exp ((1 / 2 + d) ^ 2) *
          (|Real.log x| + 3) * Real.exp (-(τ ^ 2)) := by
      rw [hA, hE]
      ring

end RHTower
