import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineDualPrimitives
import GaloisForLFunctions.HTGeometry.HalfPlanePolePushing

/-!
# Uniform normalization of the exact spline denominator

Above height `H > 0`, the factor `H^8 / (δ + ix)^8` has norm at most one.
On a window of span `C`, it differs from one by at most `8(C+δ)/H`, and
its derivative has norm at most `8/H`. These bounds transfer numerator
moment corrections to the prescribed eighth-power spline coefficients.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

def splineHeightFactor (H δ x : ℝ) : ℂ :=
  (H : ℂ)^8/((δ : ℂ)+(x : ℂ)*Complex.I)^8

lemma splineHeightFactor_eq (H δ x : ℝ) :
    splineHeightFactor H δ x=((H : ℂ)/((x : ℂ)-(δ : ℂ)*Complex.I))^8 := by
  have hz : (δ : ℂ)+(x : ℂ)*Complex.I=Complex.I*((x : ℂ)-(δ : ℂ)*Complex.I) := by
    calc
      _ = (x : ℂ)*Complex.I-(δ : ℂ)*(Complex.I*Complex.I) := by rw [Complex.I_mul_I]; ring
      _ = _ := by ring
  have hi : Complex.I^8=1 := by
    rw [show (8 : ℕ)=2*4 by rfl, pow_mul, Complex.I_sq]
    norm_num
  rw [splineHeightFactor, hz, mul_pow, hi, one_mul, div_pow]

lemma norm_height_denominator_ge (δ x : ℝ) :
    x ≤ ‖(x : ℂ)-(δ : ℂ)*Complex.I‖ := by
  have h := Complex.abs_re_le_norm ((x : ℂ)-(δ : ℂ)*Complex.I)
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero] at h
  exact (le_abs_self x).trans h

lemma norm_splineHeightFactor_le {H x : ℝ} (hH : 0 < H) (hx : H ≤ x) (δ : ℝ) :
    ‖splineHeightFactor H δ x‖ ≤ 1 := by
  rw [splineHeightFactor_eq, norm_pow]
  have hd := hx.trans (norm_height_denominator_ge δ x)
  have hdpos := hH.trans_le hd
  apply pow_le_one₀ (norm_nonneg _)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  exact (div_le_one hdpos).mpr hd

/-- The exact denominator approaches its leading height power uniformly over a bounded window. -/
theorem norm_splineHeightFactor_sub_one_le {H δ C x : ℝ} (hH : 0 < H)
    (hδ : 0 ≤ δ) (hx : H ≤ x) (hxC : x ≤ H+C) :
    ‖splineHeightFactor H δ x-1‖ ≤ 8*(C+δ)/H := by
  let w : ℂ := (x : ℂ)-(δ : ℂ)*Complex.I
  have hd : H ≤ ‖w‖ := hx.trans (norm_height_denominator_ge δ x)
  have hdpos := hH.trans_le hd
  have hw : w ≠ 0 := norm_pos_iff.mp hdpos
  have hC : 0 ≤ C := by linarith only [hx,hxC]
  have hu : ‖(H : ℂ)/w‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
    exact (div_le_one hdpos).mpr hd
  have hn : ‖(H : ℂ)-w‖ ≤ C+δ := by
    have he : (H : ℂ)-w=((H-x : ℝ) : ℂ)+(δ : ℂ)*Complex.I := by
      dsimp only [w]
      push_cast
      ring
    rw [he]
    calc
      _ ≤ ‖((H-x : ℝ) : ℂ)‖+‖(δ : ℂ)*Complex.I‖ := norm_add_le _ _
      _ = x-H+δ := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hx), abs_of_nonneg hδ]
        ring
      _ ≤ C+δ := by linarith only [hxC]
  have hbase : ‖(H : ℂ)/w-1‖ ≤ (C+δ)/H := by
    have he : (H : ℂ)/w-1=((H : ℂ)-w)/w := by field_simp
    rw [he, norm_div]
    exact (div_le_div_of_nonneg_right hn hdpos.le).trans
      (div_le_div_of_nonneg_left (add_nonneg hC hδ) hH hd)
  have hp := GaloisForLFunctions.HTGeometry.norm_pow_sub_pow_le hu
    (show ‖(1 : ℂ)‖ ≤ (1 : ℝ) by simp) 8
  simp only [one_pow, Nat.cast_ofNat, mul_one] at hp
  rw [splineHeightFactor_eq]
  exact hp.trans ((mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ℝ) ≤ 8)).trans_eq (by ring))

lemma hasDerivAt_splineHeightFactor {H δ x : ℝ} (hH : 0 < H) (hx : H ≤ x) :
    HasDerivAt (splineHeightFactor H δ)
      (-(8 : ℂ)*Complex.I*(H : ℂ)^8/((δ : ℂ)+(x : ℂ)*Complex.I)^9) x := by
  let z : ℂ := (δ : ℂ)+(x : ℂ)*Complex.I
  have hz : z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add, Complex.zero_im] at hi
    linarith only [hH,hx,hi]
  have hlin := ((hasDerivAt_id (x : ℂ)).mul_const Complex.I).const_add (δ : ℂ)
  have h := (hasDerivAt_const (x : ℂ) ((H : ℂ)^8)).div (hlin.pow 8) (pow_ne_zero 8 hz)
  have he : ((0 : ℂ)*z^8-(H : ℂ)^8*(8*z^7*(1*Complex.I)))/(z^8)^2=
      -(8 : ℂ)*Complex.I*(H : ℂ)^8/z^9 := by
    field_simp
    ring
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, Pi.pow_apply] at h
  rw [he] at h
  exact h.comp_ofReal

/-- Denominator variation contributes only an inverse-height derivative error. -/
theorem norm_splineHeightFactor_deriv_le {H δ x : ℝ} (hH : 0 < H) (hx : H ≤ x) :
    ‖-(8 : ℂ)*Complex.I*(H : ℂ)^8/((δ : ℂ)+(x : ℂ)*Complex.I)^9‖ ≤ 8/H := by
  let z : ℂ := (δ : ℂ)+(x : ℂ)*Complex.I
  have hz : H ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add] at h
    exact hx.trans ((le_abs_self x).trans h)
  have hzpos := hH.trans_le hz
  change ‖-(8 : ℂ)*Complex.I*(H : ℂ)^8/z^9‖ ≤ 8/H
  rw [norm_div, norm_mul, norm_mul, norm_neg, Complex.norm_I, mul_one, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH, norm_pow]
  norm_num only [norm_ofNat]
  calc
    _ = (8/H)*(H/‖z‖)^9 := by field_simp
    _ ≤ (8/H)*1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (div_nonneg hH.le hzpos.le) ((div_le_one hzpos).mpr hz)) (by positivity)
    _ = _ := by ring

#print axioms norm_splineHeightFactor_sub_one_le
#print axioms hasDerivAt_splineHeightFactor
#print axioms norm_splineHeightFactor_deriv_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
