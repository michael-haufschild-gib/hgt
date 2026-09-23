import GaloisForLFunctions.RHTower.XiThetaSquareRateReader
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Exact boundary energy of the infinite theta square-rate symbol

The explicit square-rate reader symbol is inner on the imaginary boundary away from the removable
origin: its sine and hyperbolic-sine terms have equal norm. Combining that identity with the exact
nonzero node slope gives a Cauchy boundary profile. The physical-rate boundary energy is exactly
`4 * sinh (pi*n)^(2 : ℕ)`, or `2/pi * sinh (pi*n)^(2 : ℕ)` in the standard half-plane normalization.

This proves the predicted boundary norm directly, without a Hardy-membership proposition.
-/

open Complex Real Set

noncomputable section

namespace RHTower

open MeasureTheory

lemma complex_sqrt_sq (z : ℂ) : (Complex.sqrt z) ^ 2 = z := by
  exact Complex.cpow_nat_inv_pow z (by norm_num)

lemma pureImag_sqrt_re_sq_eq_im_sq (t : ℝ) :
    (Complex.sqrt ((t : ℂ) * I)).re ^ 2 =
      (Complex.sqrt ((t : ℂ) * I)).im ^ 2 := by
  have h := congrArg Complex.re (complex_sqrt_sq ((t : ℂ) * I))
  simp [pow_two, Complex.mul_re] at h ⊢
  nlinarith

lemma pureImag_sqrt_re_pos {t : ℝ} (ht : t ≠ 0) :
    0 < (Complex.sqrt ((t : ℂ) * I)).re := by
  rw [Complex.sqrt_eq_real_add_ite]
  split_ifs <;> simp [Complex.mul_re] <;> positivity

lemma pureImag_sqrt_mul_I_eq_conj_or_neg_conj (t : ℝ) :
    Complex.sqrt ((t : ℂ) * I) * I =
        (starRingEnd ℂ) (Complex.sqrt ((t : ℂ) * I)) ∨
      Complex.sqrt ((t : ℂ) * I) * I =
        -(starRingEnd ℂ) (Complex.sqrt ((t : ℂ) * I)) := by
  let w := Complex.sqrt ((t : ℂ) * I)
  have hsq : w.re ^ 2 = w.im ^ 2 := pureImag_sqrt_re_sq_eq_im_sq t
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
  · right
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> linarith
  · left
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> linarith

lemma norm_sin_pureImag_sqrt_eq_norm_sinh (t : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ) * Complex.sqrt ((t : ℂ) * I))‖ =
      ‖Complex.sinh ((Real.pi : ℂ) * Complex.sqrt ((t : ℂ) * I))‖ := by
  let w := (Real.pi : ℂ) * Complex.sqrt ((t : ℂ) * I)
  have hw : w * I = (starRingEnd ℂ) w ∨ w * I = -(starRingEnd ℂ) w := by
    rcases pureImag_sqrt_mul_I_eq_conj_or_neg_conj t with h | h
    · left
      calc
        w * I = (Real.pi : ℂ) * (Complex.sqrt ((t : ℂ) * I) * I) := by
          simp only [w]; ring
        _ = (Real.pi : ℂ) * (starRingEnd ℂ) (Complex.sqrt ((t : ℂ) * I)) := by rw [h]
        _ = (starRingEnd ℂ) w := by simp [w]
    · right
      calc
        w * I = (Real.pi : ℂ) * (Complex.sqrt ((t : ℂ) * I) * I) := by
          simp only [w]; ring
        _ = (Real.pi : ℂ) * (-(starRingEnd ℂ) (Complex.sqrt ((t : ℂ) * I))) := by rw [h]
        _ = -(starRingEnd ℂ) w := by simp [w]
  have htrig : Complex.sin (w * I) = Complex.sinh w * I := Complex.sin_mul_I w
  rcases hw with hw | hw
  · calc
      ‖Complex.sin w‖ = ‖(starRingEnd ℂ) (Complex.sin w)‖ :=
        (Complex.norm_conj _).symm
      _ = ‖Complex.sin ((starRingEnd ℂ) w)‖ := by rw [Complex.sin_conj]
      _ = ‖Complex.sin (w * I)‖ := by rw [hw]
      _ = ‖Complex.sinh w * I‖ := by rw [htrig]
      _ = ‖Complex.sinh w‖ := by simp
  · calc
      ‖Complex.sin w‖ = ‖-(starRingEnd ℂ) (Complex.sin w)‖ := by
        rw [norm_neg, Complex.norm_conj]
      _ = ‖Complex.sin (-(starRingEnd ℂ) w)‖ := by
        rw [Complex.sin_neg, Complex.sin_conj]
      _ = ‖Complex.sin (w * I)‖ := by rw [hw]
      _ = ‖Complex.sinh w * I‖ := by rw [htrig]
      _ = ‖Complex.sinh w‖ := by simp

lemma sinh_pi_sqrt_pureImag_ne_zero {t : ℝ} (ht : t ≠ 0) :
    Complex.sinh ((Real.pi : ℂ) * Complex.sqrt ((t : ℂ) * I)) ≠ 0 := by
  intro hsinh
  let w := (Real.pi : ℂ) * Complex.sqrt ((t : ℂ) * I)
  have hsin : Complex.sin (w * I) = 0 := by
    rw [Complex.sin_mul_I, show Complex.sinh w = 0 by exact hsinh, zero_mul]
  rcases Complex.sin_eq_zero_iff.mp hsin with ⟨k, hk⟩
  have him := congrArg Complex.im hk
  have hwre : 0 < w.re := by
    simp only [w, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_pos Real.pi_pos (pureImag_sqrt_re_pos ht)
  simp only [mul_im, I_re, I_im, mul_zero, mul_one] at him
  simp at him
  linarith

/-- The canonical square-zero quotient has unit norm on the punctured imaginary boundary. -/
theorem norm_thetaSquareBlaschkeSymbol_mul_I {t : ℝ} (ht : t ≠ 0) :
    ‖thetaSquareBlaschkeSymbol ((t : ℂ) * I)‖ = 1 := by
  rw [thetaSquareBlaschkeSymbol, norm_div,
    norm_sin_pureImag_sqrt_eq_norm_sinh t, div_self]
  exact norm_ne_zero_iff.mpr (sinh_pi_sqrt_pureImag_ne_zero ht)

lemma norm_thetaSquare_eq (n : ℕ) : ‖thetaSquare n‖ = (n : ℝ) ^ 2 := by
  simp [thetaSquare, norm_pow]

lemma norm_thetaSquare_cpow_neg_half (n : ℕ) :
    ‖thetaSquare n ^ ((-1 : ℂ) / 2)‖ = ((n : ℝ)⁻¹) := by
  have hexp : ((-1 : ℂ) / 2) = (((-1 : ℝ) / 2 : ℝ) : ℂ) := by norm_num
  rw [hexp, Complex.norm_cpow_real, norm_thetaSquare_eq]
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring,
    Real.rpow_neg (sq_nonneg (n : ℝ))]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (Nat.cast_nonneg n)]

lemma norm_cos_pi_nat (n : ℕ) :
    ‖Complex.cos ((Real.pi : ℂ) * (n : ℂ))‖ = 1 := by
  rw [show (Real.pi : ℂ) * (n : ℂ) = (((Real.pi * n : ℝ)) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_cos, norm_real, Real.norm_eq_abs]
  rw [show Real.pi * (n : ℝ) = (n : ℝ) * Real.pi by ring, Real.cos_nat_mul_pi]
  simp

lemma norm_sinh_pi_nat {n : ℕ} (hn : 1 ≤ n) :
    ‖Complex.sinh ((Real.pi : ℂ) * (n : ℂ))‖ = Real.sinh (Real.pi * n) := by
  rw [show (Real.pi : ℂ) * (n : ℂ) = (((Real.pi * n : ℝ)) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_sinh, norm_real, Real.norm_eq_abs, abs_of_pos]
  rw [Real.sinh_pos_iff]
  exact mul_pos Real.pi_pos (by positivity)

/-- Exact norm of the simple node slope; its reciprocal is the reader amplification. -/
theorem norm_thetaSquareBlaschkeNodeSlope {n : ℕ} (hn : 1 ≤ n) :
    ‖thetaSquareBlaschkeNodeSlope n‖ =
      Real.pi / (2 * n * Real.sinh (Real.pi * n)) := by
  rw [thetaSquareBlaschkeNodeSlope, norm_div, norm_mul, norm_cos_pi_nat, one_mul,
    norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_div,
    norm_thetaSquare_cpow_neg_half n]
  norm_num
  rw [norm_sinh_pi_nat hn]
  have hnR : (0 : ℝ) < n := by positivity
  have hsinh : 0 < Real.sinh (Real.pi * n) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hnR)
  field_simp

lemma pureImag_ne_thetaSquare {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (t : ℂ) * I ≠ thetaSquare n := by
  intro h
  have hre := congrArg Complex.re h
  have hnR : (0 : ℝ) < n := by positivity
  simp [thetaSquare, pow_two, Complex.mul_re] at hre
  nlinarith

lemma norm_pureImag_sub_thetaSquare (n : ℕ) (t : ℝ) :
    ‖(t : ℂ) * I - thetaSquare n‖ =
      Real.sqrt (((n : ℝ) ^ 2) ^ 2 + t ^ 2) := by
  rw [show (t : ℂ) * I - thetaSquare n =
      ((-((n : ℝ) ^ 2) : ℝ) : ℂ) + (t : ℂ) * I by
    simp [thetaSquare]
    ring]
  rw [Complex.norm_add_mul_I]
  congr 2
  ring

/-- Exact Cauchy boundary profile of the dimensionless infinite reader symbol. -/
theorem norm_thetaSquareBlaschkeReaderSymbol_mul_I {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (ht : t ≠ 0) :
    ‖thetaSquareBlaschkeReaderSymbol n ((t : ℂ) * I)‖ =
      (2 * n * Real.sinh (Real.pi * n)) /
        (Real.pi * Real.sqrt (((n : ℝ) ^ 2) ^ 2 + t ^ 2)) := by
  rw [thetaSquareBlaschkeReaderSymbol,
    dslope_of_ne _ (pureImag_ne_thetaSquare hn t), slope_def_field,
    thetaSquareBlaschkeSymbol_zero, sub_zero, norm_mul, norm_inv, norm_div,
    norm_thetaSquareBlaschkeSymbol_mul_I ht, one_div,
    norm_thetaSquareBlaschkeNodeSlope hn, norm_pureImag_sub_thetaSquare]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnR : (0 : ℝ) < n := by positivity
  have hsinh : 0 < Real.sinh (Real.pi * n) :=
    Real.sinh_pos_iff.mpr (mul_pos hpi hnR)
  field_simp

lemma integral_inv_sq_add_sq_univ {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, (a ^ 2 + t ^ 2)⁻¹) = Real.pi / a := by
  calc
    (∫ t : ℝ, (a ^ 2 + t ^ 2)⁻¹) =
        ∫ t : ℝ, a⁻¹ ^ 2 * (1 + (t / a) ^ 2)⁻¹ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        field_simp
    _ = a⁻¹ ^ 2 * ∫ t : ℝ, (1 + (t / a) ^ 2)⁻¹ := by
      rw [MeasureTheory.integral_const_mul]
    _ = a⁻¹ ^ 2 * (|a| * ∫ t : ℝ, (1 + t ^ 2)⁻¹) := by
      congr 1
      simpa only [smul_eq_mul] using!
        (MeasureTheory.Measure.integral_comp_div (fun t : ℝ => (1 + t ^ 2)⁻¹) a)
    _ = Real.pi / a := by
      rw [integral_univ_inv_one_add_sq, abs_of_pos ha]
      field_simp

/-- Exact squared boundary norm of the dimensionless rate reader. -/
theorem integral_sq_norm_thetaSquareBlaschkeReaderSymbol_boundary {n : ℕ} (hn : 1 ≤ n) :
    (∫ t : ℝ, ‖thetaSquareBlaschkeReaderSymbol n ((t : ℂ) * I)‖ ^ 2) =
      (4 / Real.pi) * Real.sinh (Real.pi * n) ^ 2 := by
  have ht0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have hAE :
      (fun t : ℝ => ‖thetaSquareBlaschkeReaderSymbol n ((t : ℂ) * I)‖ ^ 2) =ᵐ[volume]
        (fun t : ℝ =>
          ((2 * n * Real.sinh (Real.pi * n)) ^ 2 / Real.pi ^ 2) *
            ((((n : ℝ) ^ 2) ^ 2 + t ^ 2)⁻¹)) := by
    filter_upwards [ht0] with t ht
    rw [norm_thetaSquareBlaschkeReaderSymbol_mul_I hn ht, div_pow]
    have hden :
        (Real.pi * Real.sqrt (((n : ℝ) ^ 2) ^ 2 + t ^ 2)) ^ 2 =
          Real.pi ^ 2 * (((n : ℝ) ^ 2) ^ 2 + t ^ 2) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [hden]
    field_simp
  rw [integral_congr_ae hAE, MeasureTheory.integral_const_mul,
    integral_inv_sq_add_sq_univ (sq_pos_of_pos (by positivity : (0 : ℝ) < n))]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Physical-rate boundary energy after restoring the factor of pi. -/
theorem integral_sq_norm_thetaHeatRateReaderSymbol_boundary {n : ℕ} (hn : 1 ≤ n) :
    (∫ t : ℝ, ‖thetaHeatRateReaderSymbol n ((t : ℂ) * I)‖ ^ 2) =
      4 * Real.sinh (Real.pi * n) ^ 2 := by
  let g : ℝ → ℝ := fun u => ‖thetaSquareBlaschkeReaderSymbol n ((u : ℂ) * I)‖ ^ 2
  calc
    (∫ t : ℝ, ‖thetaHeatRateReaderSymbol n ((t : ℂ) * I)‖ ^ 2) =
        ∫ t : ℝ, g (t / Real.pi) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        simp only [g, thetaHeatRateReaderSymbol]
        congr 3
        push_cast
        field_simp
    _ = |Real.pi| * ∫ u : ℝ, g u := by
      simpa only [smul_eq_mul] using
        (MeasureTheory.Measure.integral_comp_div g Real.pi)
    _ = 4 * Real.sinh (Real.pi * n) ^ 2 := by
      rw [show (∫ u : ℝ, g u) =
          (4 / Real.pi) * Real.sinh (Real.pi * n) ^ 2 by
        exact integral_sq_norm_thetaSquareBlaschkeReaderSymbol_boundary hn]
      rw [abs_of_pos Real.pi_pos]
      field_simp

/-- The physical boundary energy in the standard half-plane Hardy normalization. -/
theorem normalized_boundary_energy_thetaHeatRateReaderSymbol {n : ℕ} (hn : 1 ≤ n) :
    (1 / (2 * Real.pi)) *
        (∫ t : ℝ, ‖thetaHeatRateReaderSymbol n ((t : ℂ) * I)‖ ^ 2) =
      (2 / Real.pi) * Real.sinh (Real.pi * n) ^ 2 := by
  rw [integral_sq_norm_thetaHeatRateReaderSymbol_boundary hn]
  field_simp
  norm_num
