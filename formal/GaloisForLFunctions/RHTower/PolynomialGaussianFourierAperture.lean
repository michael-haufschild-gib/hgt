import GaloisForLFunctions.HTGeometry.ComplexGaussianPolynomialTranslation
import GaloisForLFunctions.HTGeometry.SchwartzSupL2Bound
import GaloisForLFunctions.HTGeometry.PolynomialGrowthBound
import GaloisForLFunctions.HTGeometry.FiniteRegularityWienerFamily
import GaloisForLFunctions.HTGeometry.FourierIntegralDilation
import GaloisForLFunctions.RHTower.StripHorizontalShift

/-!
# Polynomial--Gaussian Fourier aperture

This file proves the coefficient-uniform Fourier estimate required by Route U's C43-Y/PDH
prime aperture.  For every real polynomial `P` and every signed frequency `η`, including the zero
and constant cases,

`‖𝓕 (P² exp (-2π·²)) η‖ ≤ exp (-πη²/2 + |η| sqrt(4π natDegree P)) ‖P exp(-π·²)‖₂²`.

The proof is analytic rather than computational.  An explicit coefficient-dependent majorant
justifies a lower horizontal contour shift.  Completing the square turns the shifted integral into
the squared `L²` norm of a complex-translated polynomial Gaussian.  The already closed sharp
translation theorem removes every coefficient dependence.  Conjugation supplies negative
frequencies.
-/

open scoped Real SchwartzMap FourierTransform
open Complex Real MeasureTheory

noncomputable section

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- Real polynomial--Gaussian energy, embedded in `ℂ` for the Fourier integral. -/
def polynomialGaussianEnergy (P : Polynomial ℝ) (x : ℝ) : ℂ :=
  (((P.eval x) ^ 2 * Real.exp (-(2 * Real.pi * x ^ 2)) : ℝ) : ℂ)

@[simp] theorem polynomialGaussianEnergy_apply (P : Polynomial ℝ) (x : ℝ) :
    polynomialGaussianEnergy P x =
      (((P.eval x) ^ 2 * Real.exp (-(2 * Real.pi * x ^ 2)) : ℝ) : ℂ) := by
  rfl

/-- Entire continuation of the Fourier integrand. -/
def polynomialGaussianFourierEntire (P : Polynomial ℝ) (η : ℝ) (z : ℂ) : ℂ :=
  (P.map (algebraMap ℝ ℂ)).eval z ^ 2 *
    Complex.exp (-(2 * (Real.pi : ℂ) * z ^ 2) -
      2 * (Real.pi : ℂ) * Complex.I * (η : ℂ) * z)

theorem polynomialGaussianFourierEntire_real_apply (P : Polynomial ℝ) (η x : ℝ) :
    polynomialGaussianFourierEntire P η (x : ℂ) =
      Complex.exp ((↑(-2 * Real.pi * x * η) : ℂ) * Complex.I) *
        polynomialGaussianEnergy P x := by
  rw [polynomialGaussianFourierEntire, polynomialGaussianEnergy_apply]
  have hpoly : (P.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((P.eval x : ℝ) : ℂ) := by
    simpa using Polynomial.eval_map_apply (f := algebraMap ℝ ℂ) (p := P) x
  rw [hpoly]
  push_cast
  have harg :
      -(2 * (Real.pi : ℂ) * (x : ℂ) ^ 2) -
          2 * (Real.pi : ℂ) * Complex.I * (η : ℂ) * (x : ℂ) =
        ((-2 * Real.pi * x * η : ℝ) : ℂ) * Complex.I +
          -(2 * (Real.pi : ℂ) * (x : ℂ) ^ 2) := by
    push_cast
    ring
  rw [harg, Complex.exp_add]
  have hphase :
      ((-2 * Real.pi * x * η : ℝ) : ℂ) * Complex.I =
        -(Complex.I * (Real.pi : ℂ) * (x : ℂ) * (η : ℂ) * 2) := by
    push_cast
    ring
  rw [hphase]
  ring

/-- The pointwise mass of the energy is exactly the squared Gaussian `L²` norm. -/
theorem integral_norm_polynomialGaussianEnergy (P : Polynomial ℝ) :
    (∫ x : ℝ, ‖polynomialGaussianEnergy P x‖) =
      ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  rw [norm_toLp_sq_eq_integral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change ‖polynomialGaussianEnergy P x‖ = ‖polyGaussSchwartz P x‖ ^ 2
  rw [polynomialGaussianEnergy_apply, polyGaussSchwartz_apply]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (gaussReal_pos x), gaussReal]
  rw [mul_pow, sq_abs, ← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

private theorem one_add_pow_le_exp {t : ℝ} (ht : 0 ≤ t) (N : ℕ) :
    (1 + t) ^ N ≤ Real.exp ((N : ℝ) * t) := by
  have h1 : (1 : ℝ) + t ≤ Real.exp t := by
    linarith [Real.add_one_le_exp t]
  calc
    (1 + t) ^ N ≤ (Real.exp t) ^ N := pow_le_pow_left₀ (by linarith) h1 N
    _ = Real.exp ((N : ℝ) * t) := by rw [← Real.exp_nat_mul]

/-- Explicit strip majorant.  Its coefficient dependence is used only to justify contour motion. -/
def polynomialGaussianStripConstant (P : Polynomial ℝ) (c : ℝ) : ℝ :=
  let PC := P.map (algebraMap ℝ ℂ)
  (coeffNormSum PC) ^ 2 * Real.exp
    (2 * P.natDegree * c + 2 * Real.pi * c ^ 2 +
      (2 * P.natDegree + 1 : ℝ) ^ 2 / 8)

theorem norm_polynomialGaussianFourierEntire_le_strip
    (P : Polynomial ℝ) {η c : ℝ} (hη : 0 ≤ η) (hc : 0 ≤ c)
    (z : ℂ) (hzlow : -c ≤ z.im) (hzup : z.im ≤ 0) :
    ‖polynomialGaussianFourierEntire P η z‖ ≤
      polynomialGaussianStripConstant P c * Real.exp (-|z.re|) := by
  let PC : Polynomial ℂ := P.map (algebraMap ℝ ℂ)
  let S : ℝ := coeffNormSum PC
  let d : ℕ := P.natDegree
  have hS : 0 ≤ S := coeffNormSum_nonneg PC
  have himabs : |z.im| ≤ c := by
    rw [abs_of_nonpos hzup]
    linarith
  have hznorm : ‖z‖ ≤ |z.re| + c := by
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ |z.re| + c := by linarith
  have ht : 0 ≤ |z.re| + c := add_nonneg (abs_nonneg _) hc
  have hbase : 1 + ‖z‖ ≤ 1 + (|z.re| + c) := by linarith
  have hdeg : PC.natDegree = d := by
    exact Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective P
  have hpoly0 := norm_eval_le_coeffNormSum PC z
  rw [hdeg] at hpoly0
  change ‖PC.eval z‖ ≤ S * (1 + ‖z‖) ^ d at hpoly0
  have hpoly : ‖PC.eval z‖ ^ 2 ≤
      S ^ 2 * Real.exp ((2 * d : ℕ) * (|z.re| + c)) := by
    calc
      ‖PC.eval z‖ ^ 2 ≤ (S * (1 + ‖z‖) ^ d) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hpoly0 2
      _ = S ^ 2 * (1 + ‖z‖) ^ (2 * d) := by ring
      _ ≤ S ^ 2 * (1 + (|z.re| + c)) ^ (2 * d) := by gcongr
      _ ≤ S ^ 2 * Real.exp ((2 * d : ℕ) * (|z.re| + c)) := by
        gcongr
        exact one_add_pow_le_exp ht (2 * d)
  have hexpre :
      (-(2 * (Real.pi : ℂ) * z ^ 2) -
          2 * (Real.pi : ℂ) * Complex.I * (η : ℂ) * z).re =
        -2 * Real.pi * z.re ^ 2 + 2 * Real.pi * z.im ^ 2 +
          2 * Real.pi * η * z.im := by
    rw [show z ^ 2 = z * z by ring]
    simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    norm_num
    ring
  have himsq : z.im ^ 2 ≤ c ^ 2 := by
    nlinarith [sq_nonneg (z.im + c), sq_nonneg z.im]
  have hexparg :
      -2 * Real.pi * z.re ^ 2 + 2 * Real.pi * z.im ^ 2 +
          2 * Real.pi * η * z.im ≤
        -2 * Real.pi * z.re ^ 2 + 2 * Real.pi * c ^ 2 := by
    have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    have hcoef : 0 ≤ 2 * Real.pi * η := by positivity
    have hlast : 2 * Real.pi * η * z.im ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoef hzup
    nlinarith
  have hvertex :
      (2 * d : ℝ) * |z.re| - 2 * Real.pi * z.re ^ 2 ≤
        -|z.re| + (2 * d + 1 : ℝ) ^ 2 / 8 := by
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have habsq : |z.re| ^ 2 = z.re ^ 2 := sq_abs _
    have hs := sq_nonneg (2 * |z.re| - (2 * d + 1 : ℝ) / 2)
    nlinarith [habsq,
      mul_nonneg (by positivity : 0 ≤ 2 * (Real.pi - 1)) (sq_nonneg z.re)]
  rw [polynomialGaussianFourierEntire, norm_mul, norm_pow, Complex.norm_exp, hexpre]
  calc
    ‖PC.eval z‖ ^ 2 * Real.exp
        (-2 * Real.pi * z.re ^ 2 + 2 * Real.pi * z.im ^ 2 +
          2 * Real.pi * η * z.im)
      ≤ (S ^ 2 * Real.exp ((2 * d : ℕ) * (|z.re| + c))) *
          Real.exp (-2 * Real.pi * z.re ^ 2 + 2 * Real.pi * c ^ 2) := by
        exact mul_le_mul hpoly (Real.exp_le_exp.mpr hexparg)
          (Real.exp_nonneg _) (by positivity)
    _ = S ^ 2 * Real.exp
          (2 * d * c + 2 * Real.pi * c ^ 2 +
            ((2 * d : ℝ) * |z.re| - 2 * Real.pi * z.re ^ 2)) := by
        conv_lhs => rw [mul_assoc, ← Real.exp_add]
        congr 1
        push_cast
        ring
    _ ≤ S ^ 2 * Real.exp
          (2 * d * c + 2 * Real.pi * c ^ 2 +
            (-|z.re| + (2 * d + 1 : ℝ) ^ 2 / 8)) := by gcongr
    _ = polynomialGaussianStripConstant P c * Real.exp (-|z.re|) := by
        rw [polynomialGaussianStripConstant]
        simp only [PC, S, d]
        conv_rhs => rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring

/-- The Fourier integrand can be shifted to the exact completing-square line. -/
theorem integral_polynomialGaussianFourierEntire_shift
    (P : Polynomial ℝ) {η : ℝ} (hη : 0 ≤ η) :
    (∫ x : ℝ, polynomialGaussianFourierEntire P η
        ((x : ℂ) - ((η / 2 : ℝ) : ℂ) * Complex.I)) =
      ∫ x : ℝ, polynomialGaussianFourierEntire P η (x : ℂ) := by
  apply integral_horizontal_shift_neg_of_lower_decay
    (c := η / 2) (C := polynomialGaussianStripConstant P (η / 2)) (r := 1)
  · positivity
  · norm_num
  · intro z _ _
    unfold polynomialGaussianFourierEntire
    fun_prop
  · intro z hzlow hzup
    simpa only [one_mul] using
      norm_polynomialGaussianFourierEntire_le_strip P hη (by positivity) z hzlow hzup

/-- Exact completing-square identity on the shifted line. -/
theorem polynomialGaussianFourierEntire_shift_apply
    (P : Polynomial ℝ) (η x : ℝ) :
    polynomialGaussianFourierEntire P η
        ((x : ℂ) - ((η / 2 : ℝ) : ℂ) * Complex.I) =
      (Real.exp (-(Real.pi * η ^ 2 / 2)) : ℂ) *
        (complexTranslatedPolyGauss P (-((η / 2 : ℝ) : ℂ) * Complex.I) x) ^ 2 := by
  rw [polynomialGaussianFourierEntire, complexTranslatedPolyGauss_apply]
  have heval :
      (P.map (algebraMap ℝ ℂ)).eval
          ((x : ℂ) - ((η / 2 : ℝ) : ℂ) * Complex.I) =
        Polynomial.eval₂ (algebraMap ℝ ℂ)
          ((x : ℂ) + -((η / 2 : ℝ) : ℂ) * Complex.I) P := by
    rw [Polynomial.eval₂_eq_eval_map]
    congr 1
    ring
  rw [heval]
  have hgauss : ((gaussReal x : ℝ) : ℂ) ^ 2 =
      Complex.exp (-(2 * (Real.pi : ℂ) * (x : ℂ) ^ 2)) := by
    rw [gaussReal, Complex.ofReal_exp]
    push_cast
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow, hgauss, Complex.ofReal_exp]
  have hexp :
      -(2 * (Real.pi : ℂ) *
          ((x : ℂ) - ((η / 2 : ℝ) : ℂ) * Complex.I) ^ 2) -
          2 * (Real.pi : ℂ) * Complex.I * (η : ℂ) *
            ((x : ℂ) - ((η / 2 : ℝ) : ℂ) * Complex.I) =
        ((-(Real.pi * η ^ 2 / 2) : ℝ) : ℂ) +
          -(2 * (Real.pi : ℂ) * (x : ℂ) ^ 2) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hexp, Complex.exp_add]
  ring

theorem norm_fourier_polynomialGaussianEnergy_le_of_nonneg
    (P : Polynomial ℝ) {η : ℝ} (hη : 0 ≤ η) :
    ‖𝓕 (polynomialGaussianEnergy P) η‖ ≤
      Real.exp (-(Real.pi * η ^ 2 / 2) +
        η * Real.sqrt (4 * Real.pi * P.natDegree)) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hreal := integral_polynomialGaussianFourierEntire_shift P hη
  have hunshift :
      (∫ x : ℝ, Complex.exp ((↑(-2 * Real.pi * x * η) : ℂ) * Complex.I) •
          polynomialGaussianEnergy P x) =
        ∫ x : ℝ, polynomialGaussianFourierEntire P η (x : ℂ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change Complex.exp ((↑(-2 * Real.pi * x * η) : ℂ) * Complex.I) *
      polynomialGaussianEnergy P x = polynomialGaussianFourierEntire P η (x : ℂ)
    exact (polynomialGaussianFourierEntire_real_apply P η x).symm
  rw [hunshift, ← hreal]
  have hshiftpoint (x : ℝ) :
      polynomialGaussianFourierEntire P η
          ((x : ℂ) - ((η / 2 : ℝ) : ℂ) * Complex.I) =
        (Real.exp (-(Real.pi * η ^ 2 / 2)) : ℂ) *
          (complexTranslatedPolyGauss P
            (-((η / 2 : ℝ) : ℂ) * Complex.I) x) ^ 2 :=
    polynomialGaussianFourierEntire_shift_apply P η x
  rw [integral_congr_ae (Filter.Eventually.of_forall hshiftpoint),
    MeasureTheory.integral_const_mul]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  refine le_trans (mul_le_mul_of_nonneg_left
    (norm_integral_le_integral_norm _) (Real.exp_nonneg _)) ?_
  have hmass :
      (∫ x : ℝ, ‖complexTranslatedPolyGauss P
          (-((η / 2 : ℝ) : ℂ) * Complex.I) x ^ 2‖) =
        ‖(complexTranslatedPolyGauss P
          (-((η / 2 : ℝ) : ℂ) * Complex.I)).toLp 2
            (volume : Measure ℝ)‖ ^ 2 := by
    rw [norm_toLp_sq_eq_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change ‖complexTranslatedPolyGauss P
      (-((η / 2 : ℝ) : ℂ) * Complex.I) x ^ 2‖ =
        ‖complexTranslatedPolyGauss P
          (-((η / 2 : ℝ) : ℂ) * Complex.I) x‖ ^ 2
    rw [norm_pow]
  rw [hmass]
  have htrans := norm_complexTranslatedPolyGauss_le P
    (-((η / 2 : ℝ) : ℂ) * Complex.I)
  have hnormz : ‖-((η / 2 : ℝ) : ℂ) * Complex.I‖ = η / 2 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), Complex.norm_I, mul_one]
  rw [hnormz] at htrans
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htrans 2
  calc
    Real.exp (-(Real.pi * η ^ 2 / 2)) *
        ‖(complexTranslatedPolyGauss P
          (-((η / 2 : ℝ) : ℂ) * Complex.I)).toLp 2 volume‖ ^ 2
      ≤ Real.exp (-(Real.pi * η ^ 2 / 2)) *
          (Real.exp (η / 2 * Real.sqrt (4 * Real.pi * P.natDegree)) *
            ‖(polyGaussSchwartz P).toLp 2 volume‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_nonneg _)
    _ = Real.exp (-(Real.pi * η ^ 2 / 2) +
          η * Real.sqrt (4 * Real.pi * P.natDegree)) *
          ‖(polyGaussSchwartz P).toLp 2 volume‖ ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]
        conv_lhs => rw [← mul_assoc, ← Real.exp_add]
        congr 1
        norm_num
        ring

/-- **Polynomial--Gaussian Fourier aperture (FGA.1).**  Exact signed-frequency form. -/
theorem norm_fourier_polynomialGaussianEnergy_le (P : Polynomial ℝ) (η : ℝ) :
    ‖𝓕 (polynomialGaussianEnergy P) η‖ ≤
      Real.exp (-(Real.pi * η ^ 2 / 2) +
        |η| * Real.sqrt (4 * Real.pi * P.natDegree)) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  rcases lt_or_ge η 0 with hηneg | hη
  · have hpos : 0 ≤ -η := by linarith
    have hbound := norm_fourier_polynomialGaussianEnergy_le_of_nonneg P hpos
    have hconj := fourier_neg_eq_conj
      (f := polynomialGaussianEnergy P)
      (fun x => Complex.conj_ofReal _) (-η)
    have hnorm : ‖𝓕 (polynomialGaussianEnergy P) η‖ =
        ‖𝓕 (polynomialGaussianEnergy P) (-η)‖ := by
      rw [neg_neg] at hconj
      rw [hconj]
      simp
    rw [hnorm]
    convert hbound using 1
    · rw [abs_of_neg hηneg]
      ring
  · simpa [abs_of_nonneg hη] using
      norm_fourier_polynomialGaussianEnergy_le_of_nonneg P hη

/-! ## Exact Route-U scaling constants -/

private theorem routeU_sqrt_linear_identity (d : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.sqrt (2 * Real.pi / t) / (2 * Real.pi) *
        Real.sqrt (4 * Real.pi * (2 * d : ℕ)) =
      2 * Real.sqrt d / Real.sqrt t := by
  have hsδ : Real.sqrt (2 * Real.pi / t) ^ 2 = 2 * Real.pi / t := by
    rw [Real.sq_sqrt]
    positivity
  have hsD : Real.sqrt (4 * Real.pi * (2 * d : ℕ)) ^ 2 =
      4 * Real.pi * (2 * d : ℕ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsd : Real.sqrt (d : ℝ) ^ 2 = d := by
    rw [Real.sq_sqrt]
    positivity
  have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hL0 : 0 ≤ Real.sqrt (2 * Real.pi / t) / (2 * Real.pi) *
      Real.sqrt (4 * Real.pi * (2 * d : ℕ)) := by positivity
  have hR0 : 0 ≤ 2 * Real.sqrt d / Real.sqrt t := by positivity
  apply (sq_eq_sq₀ hL0 hR0).mp
  conv_rhs => rw [div_pow, mul_pow, hsd, hst]
  rw [mul_pow, div_pow, hsδ, hsD]
  push_cast
  field_simp
  ring

private theorem routeU_frequency_exponent_identity
    (d : ℕ) {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    -(Real.pi * (Real.sqrt (2 * Real.pi / t) * (ξ / (2 * Real.pi))) ^ 2 / 2) +
        |Real.sqrt (2 * Real.pi / t) * (ξ / (2 * Real.pi))| *
          Real.sqrt (4 * Real.pi * (2 * d : ℕ)) =
      -(ξ ^ 2 / (4 * t)) + 2 * Real.sqrt d * |ξ| / Real.sqrt t := by
  have hδ : 0 < Real.sqrt (2 * Real.pi / t) := Real.sqrt_pos.2 (by positivity)
  have hδsq : Real.sqrt (2 * Real.pi / t) ^ 2 = 2 * Real.pi / t := by
    rw [Real.sq_sqrt]
    positivity
  have habs :
      |Real.sqrt (2 * Real.pi / t) * (ξ / (2 * Real.pi))| =
        Real.sqrt (2 * Real.pi / t) / (2 * Real.pi) * |ξ| := by
    rw [abs_mul, abs_div, abs_of_pos hδ, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hquad :
      Real.pi * (Real.sqrt (2 * Real.pi / t) * (ξ / (2 * Real.pi))) ^ 2 / 2 =
        ξ ^ 2 / (4 * t) := by
    rw [mul_pow, hδsq]
    field_simp
    ring
  rw [habs]
  rw [show Real.sqrt (2 * Real.pi / t) / (2 * Real.pi) * |ξ| *
      Real.sqrt (4 * Real.pi * (2 * d : ℕ)) =
      (Real.sqrt (2 * Real.pi / t) / (2 * Real.pi) *
        Real.sqrt (4 * Real.pi * (2 * d : ℕ))) * |ξ| by ring]
  rw [routeU_sqrt_linear_identity d ht]
  rw [hquad]
  ring

/-- Route U's normalized polynomial after `x = sqrt(2π/t) y`. -/
def routeURescaledEvenPolynomial (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    Polynomial ℝ :=
  (evenSquarePolynomial Q).comp
    (Polynomial.C (Real.sqrt (2 * Real.pi / (t : ℝ))) * Polynomial.X)

@[simp] theorem natDegree_routeURescaledEvenPolynomial
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    (routeURescaledEvenPolynomial Q t).natDegree = 2 * Q.natDegree := by
  rw [routeURescaledEvenPolynomial, Polynomial.natDegree_comp,
    Polynomial.natDegree_C_mul_X]
  · rw [natDegree_evenSquarePolynomial, mul_one]
  · exact (Real.sqrt_pos.2 (div_pos (by positivity) t.property)).ne'

/-- Native Route-U heat-filter density `Q(x²)² exp(-t x²)`. -/
def routeUPolynomialGaussianDensity
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (x : ℝ) : ℂ :=
  ((((evenSquarePolynomial Q).eval x) ^ 2 * Real.exp (-((t : ℝ) * x ^ 2)) : ℝ) : ℂ)

theorem routeUPolynomialGaussianDensity_eq_dilate
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (x : ℝ) :
    routeUPolynomialGaussianDensity Q t x =
      polynomialGaussianEnergy (routeURescaledEvenPolynomial Q t)
        (x / Real.sqrt (2 * Real.pi / (t : ℝ))) := by
  let δ : ℝ := Real.sqrt (2 * Real.pi / (t : ℝ))
  have harg : 0 ≤ 2 * Real.pi / (t : ℝ) :=
    (div_pos (by positivity) t.property).le
  have hδ : 0 < δ := Real.sqrt_pos.2 (div_pos (by positivity) t.property)
  have hδsq : δ ^ 2 = 2 * Real.pi / (t : ℝ) := by
    change Real.sqrt (2 * Real.pi / (t : ℝ)) ^ 2 = _
    exact Real.sq_sqrt harg
  rw [routeUPolynomialGaussianDensity, polynomialGaussianEnergy,
    routeURescaledEvenPolynomial, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  have heval : (evenSquarePolynomial Q).eval (δ * (x / δ)) =
      (evenSquarePolynomial Q).eval x := by
    rw [mul_div_cancel₀ x hδ.ne']
  rw [heval]
  push_cast
  congr 2
  have hexp : 2 * Real.pi * (x / δ) ^ 2 = (t : ℝ) * x ^ 2 := by
    calc
      2 * Real.pi * (x / δ) ^ 2 = (2 * Real.pi / δ ^ 2) * x ^ 2 := by
        field_simp
      _ = (t : ℝ) * x ^ 2 := by
        rw [hδsq]
        field_simp
  have hexpC := congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hexp
  push_cast at hexpC
  change -((t : ℂ) * (x : ℂ) ^ 2) =
    -(2 * (Real.pi : ℂ) * ((x : ℂ) / (δ : ℂ)) ^ 2)
  exact congrArg Neg.neg hexpC.symm

/-- Native unnormalized Fourier transform used by C43-Y and PDH.9. -/
def routeUPolynomialGaussianFourier
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (((-(ξ * x) : ℝ) : ℂ) * Complex.I) *
    routeUPolynomialGaussianDensity Q t x

/-- Native mass of the Route-U polynomial--Gaussian source. -/
def routeUPolynomialGaussianMass
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) : ℝ :=
  ∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t x‖

theorem routeUPolynomialGaussianFourier_eq_fourier
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (ξ : ℝ) :
    routeUPolynomialGaussianFourier Q t ξ =
      𝓕 (routeUPolynomialGaussianDensity Q t) (ξ / (2 * Real.pi)) := by
  rw [routeUPolynomialGaussianFourier, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change Complex.exp (((-(ξ * x) : ℝ) : ℂ) * Complex.I) *
      routeUPolynomialGaussianDensity Q t x =
    Complex.exp ((↑(-2 * Real.pi * x * (ξ / (2 * Real.pi))) : ℂ) * Complex.I) *
      routeUPolynomialGaussianDensity Q t x
  congr 2
  push_cast
  field_simp

theorem routeUPolynomialGaussianMass_eq
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    routeUPolynomialGaussianMass Q t =
      Real.sqrt (2 * Real.pi / (t : ℝ)) *
        ‖(polyGaussSchwartz (routeURescaledEvenPolynomial Q t)).toLp 2
          (volume : Measure ℝ)‖ ^ 2 := by
  let δ : ℝ := Real.sqrt (2 * Real.pi / (t : ℝ))
  have hδ : 0 < δ := Real.sqrt_pos.2 (div_pos (by positivity) t.property)
  rw [routeUPolynomialGaussianMass]
  have hpoint : (fun x : ℝ => ‖routeUPolynomialGaussianDensity Q t x‖) =
      fun x : ℝ => ‖polynomialGaussianEnergy (routeURescaledEvenPolynomial Q t) (x / δ)‖ := by
    funext x
    rw [routeUPolynomialGaussianDensity_eq_dilate]
  rw [hpoint]
  change (∫ x : ℝ, (fun y : ℝ =>
    ‖polynomialGaussianEnergy (routeURescaledEvenPolynomial Q t) y‖) (x / δ)) =
      δ * ‖(polyGaussSchwartz (routeURescaledEvenPolynomial Q t)).toLp 2 volume‖ ^ 2
  calc
    (∫ x : ℝ, (fun y : ℝ =>
        ‖polynomialGaussianEnergy (routeURescaledEvenPolynomial Q t) y‖) (x / δ)) =
      |δ| • ∫ y : ℝ,
        ‖polynomialGaussianEnergy (routeURescaledEvenPolynomial Q t) y‖ :=
      MeasureTheory.Measure.integral_comp_div
        (fun y : ℝ => ‖polynomialGaussianEnergy
          (routeURescaledEvenPolynomial Q t) y‖) δ
    _ = δ * ‖(polyGaussSchwartz (routeURescaledEvenPolynomial Q t)).toLp 2 volume‖ ^ 2 := by
      rw [abs_of_pos hδ, smul_eq_mul, integral_norm_polynomialGaussianEnergy]

theorem routeUPolynomialGaussianMass_nonneg
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    0 ≤ routeUPolynomialGaussianMass Q t := by
  rw [routeUPolynomialGaussianMass_eq]
  positivity

/-- **Exact native Route-U aperture before division.** -/
theorem norm_routeUPolynomialGaussianFourier_le
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (ξ : ℝ) :
    ‖routeUPolynomialGaussianFourier Q t ξ‖ ≤
      Real.exp (-(ξ ^ 2 / (4 * (t : ℝ))) +
        2 * Real.sqrt Q.natDegree * |ξ| / Real.sqrt (t : ℝ)) *
        routeUPolynomialGaussianMass Q t := by
  let δ : ℝ := Real.sqrt (2 * Real.pi / (t : ℝ))
  let R : Polynomial ℝ := routeURescaledEvenPolynomial Q t
  let η : ℝ := ξ / (2 * Real.pi)
  have hδ : 0 < δ := Real.sqrt_pos.2 (div_pos (by positivity) t.property)
  have hdegree : R.natDegree = 2 * Q.natDegree :=
    natDegree_routeURescaledEvenPolynomial Q t
  have hdensity : routeUPolynomialGaussianDensity Q t =
      fun x : ℝ => polynomialGaussianEnergy R (x / δ) := by
    funext x
    exact routeUPolynomialGaussianDensity_eq_dilate Q t x
  have hscale := fourierIntegral_comp_div (polynomialGaussianEnergy R) δ hδ η
  have haperture := norm_fourier_polynomialGaussianEnergy_le R (δ * η)
  have hnorm : ‖routeUPolynomialGaussianFourier Q t ξ‖ =
      δ * ‖𝓕 (polynomialGaussianEnergy R) (δ * η)‖ := by
    rw [routeUPolynomialGaussianFourier_eq_fourier, show ξ / (2 * Real.pi) = η from rfl,
      hdensity, hscale, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
  rw [hnorm]
  refine le_trans (mul_le_mul_of_nonneg_left haperture hδ.le) ?_
  rw [hdegree]
  have hexponent := routeU_frequency_exponent_identity Q.natDegree t.property ξ
  change δ *
      (Real.exp (-(Real.pi * (δ * η) ^ 2 / 2) +
          |δ * η| * Real.sqrt (4 * Real.pi * (2 * Q.natDegree : ℕ))) *
        ‖(polyGaussSchwartz R).toLp 2 volume‖ ^ 2) ≤ _
  rw [show δ * η = Real.sqrt (2 * Real.pi / (t : ℝ)) *
      (ξ / (2 * Real.pi)) from rfl, hexponent]
  rw [routeUPolynomialGaussianMass_eq]
  simp only [δ, R]
  rw [mul_assoc, mul_left_comm]

/-- **Route-U C43-Y/PDH.9 aperture (FGA.2).**

The statement is closed and unconditional: positivity of `t` is encoded in its type, and no
nonzero-polynomial or positive-mass premise is needed. -/
theorem routeUPolynomialGaussianFourier_div_mass_le
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (ξ : ℝ) :
    ‖routeUPolynomialGaussianFourier Q t ξ‖ /
        routeUPolynomialGaussianMass Q t ≤
      Real.exp (-(ξ ^ 2 / (4 * (t : ℝ))) +
        2 * Real.sqrt Q.natDegree * |ξ| / Real.sqrt (t : ℝ)) := by
  by_cases hmass : routeUPolynomialGaussianMass Q t = 0
  · rw [hmass, div_zero]
    positivity
  · rw [div_le_iff₀ (lt_of_le_of_ne (routeUPolynomialGaussianMass_nonneg Q t)
      (Ne.symm hmass))]
    exact norm_routeUPolynomialGaussianFourier_le Q t ξ

end RHTower
