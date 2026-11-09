import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PositiveTailIsolation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Positive-kernel averaging preserves local trace floors up to an explicit
Chernoff tail cost. Logarithmic absolute moment growth gives exponentially
small leakage from windows of radius `8 log(T+2)`. -/

open MeasureTheory Real
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- A strip envelope factors into a height factor and a translation factor. -/
theorem exp_abs_add_le {D : ℝ} (hD : 0 ≤ D) (t x : ℝ) :
    Real.exp (D * |t + x|) ≤ Real.exp (D * |t|) * Real.exp (D * |x|) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ D * (|t| + |x|) := mul_le_mul_of_nonneg_left (abs_add_le t x) hD
    _ = _ := by ring

/-- One absolute exponential moment dominates convolution with a continuous
trace satisfying a global strip envelope. -/
theorem integrable_kernel_of_strip_bound {F k : ℝ → ℝ} {A D : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hFc : Continuous F) (hkc : Continuous k)
    (hm : Integrable fun x => Real.exp (D * |x|) * |k x|)
    (hF : ∀ u, |F u| ≤ A * Real.exp (D * |u|)) (t : ℝ) :
    Integrable fun x => k x * F (t + x) := by
  apply (hm.const_mul (A * Real.exp (D * |t|))).mono'
    (show Continuous (fun x => k x * F (t + x)) by fun_prop).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |k x| * (A * Real.exp (D * |t + x|)) :=
      mul_le_mul_of_nonneg_left (hF (t + x)) (abs_nonneg _)
    _ ≤ |k x| * (A * (Real.exp (D * |t|) * Real.exp (D * |x|))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (exp_abs_add_le hD t x) hA) (abs_nonneg _)
    _ = _ := by ring

/-- An exponential tail estimate converts a local lower bound into a global
pointwise minorant suitable for integration against a positive kernel. -/
theorem local_floor_pointwise {F k : ℝ → ℝ} {A D K q R t : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hK : 0 ≤ K) (hq : 0 ≤ q)
    (hk : ∀ x, 0 ≤ k x)
    (hF : ∀ u, |F u| ≤ A * Real.exp (D * |u|))
    (hlocal : ∀ x, |x| ≤ R → -K ≤ F (t + x)) (x : ℝ) :
    -K * k x - (A * Real.exp (D * |t| - q * R)) *
      (Real.exp ((D + q) * |x|) * k x) ≤ k x * F (t + x) := by
  have hkx := hk x
  by_cases hx : |x| ≤ R
  · have hf := mul_le_mul_of_nonneg_left (hlocal x hx) (hk x)
    have he : 0 ≤ (A * Real.exp (D * |t| - q * R)) *
        (Real.exp ((D + q) * |x|) * k x) := by positivity
    nlinarith only [hf, he]
  · have hqR : q * R ≤ q * |x| := mul_le_mul_of_nonneg_left (le_of_not_ge hx) hq
    have he : A * Real.exp (D * |t + x|) ≤
        A * Real.exp (D * |t| - q * R) * Real.exp ((D + q) * |x|) := by
      rw [mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ hA
      apply Real.exp_le_exp.mpr
      have hab := mul_le_mul_of_nonneg_left (abs_add_le t x) hD
      nlinarith only [hab, hqR]
    have hf : -(A * Real.exp (D * |t + x|)) ≤ F (t + x) :=
      (neg_le_neg (hF (t + x))).trans (neg_abs_le _)
    have hmul := mul_le_mul_of_nonneg_left ((neg_le_neg he).trans hf) (hk x)
    have hKx := mul_nonneg hK (hk x)
    nlinarith only [hmul, hKx]

/-- A positive kernel preserves a local trace floor up to its Chernoff tail cost. -/
theorem positive_kernel_local_floor {F k : ℝ → ℝ} {A D K q R t : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hK : 0 ≤ K) (hq : 0 ≤ q)
    (hk : ∀ x, 0 ≤ k x) (hki : Integrable k)
    (hkm : Integrable fun x => Real.exp ((D + q) * |x|) * k x)
    (hFi : Integrable fun x => k x * F (t + x))
    (hF : ∀ u, |F u| ≤ A * Real.exp (D * |u|))
    (hlocal : ∀ x, |x| ≤ R → -K ≤ F (t + x)) :
    -K * (∫ x, k x) - A * Real.exp (D * |t| - q * R) *
      (∫ x, Real.exp ((D + q) * |x|) * k x) ≤ ∫ x, k x * F (t + x) := by
  have hi := integral_mono ((hki.const_mul (-K)).sub
    (hkm.const_mul (A * Real.exp (D * |t| - q * R)))) hFi
    (local_floor_pointwise hA hD hK hq hk hF hlocal)
  simpa only [Pi.sub_apply, integral_sub (hki.const_mul (-K))
    (hkm.const_mul (A * Real.exp (D * |t| - q * R))), integral_const_mul] using hi

#print axioms positive_kernel_local_floor

/-- The logarithmic theta moment cost at parameter `b+T` is at most
`6 T log(T+2)` once `0≤b≤T` and `T≥6`. -/
theorem logarithmic_moment_cost_le {b T : ℝ} (hb : 0 ≤ b) (hbT : b ≤ T)
    (hT : 6 ≤ T) :
    (b + T + 6) * Real.log (b + T + 6) ≤ 6 * T * Real.log (T + 2) := by
  have ha : b + T + 6 ≤ 3 * T := by linarith only [hbT, hT]
  have ha0 : 0 < b + T + 6 := by linarith only [hb, hT]
  have hlog : Real.log (b + T + 6) ≤ 2 * Real.log (T + 2) := by
    have hh := Real.log_le_log ha0
      (show b + T + 6 ≤ (T + 2) ^ 2 by nlinarith only [ha, hT, sq_nonneg T])
    rw [Real.log_pow] at hh
    norm_num at hh
    exact hh
  have hm := mul_le_mul ha hlog (Real.log_nonneg (by linarith only [hb, hT]))
    (show 0 ≤ 3 * T by linarith only [hT])
  calc
    _ ≤ (3 * T) * (2 * Real.log (T + 2)) := hm
    _ = _ := by ring

/-- A universal logarithmic radius pays for theta moment growth, leaving
exponential decay in the observation height. -/
theorem logarithmic_chernoff_exponent_le {b D T B t : ℝ}
    (hb : 0 ≤ b) (hbT : b ≤ T) (hD : 0 ≤ D) (hT : 6 ≤ T)
    (hE : D + 1 ≤ Real.log (T + 2)) (ht : |t| ≤ T + B) :
    D * |t| - T * (8 * Real.log (T + 2)) +
      (b + T + 6) * Real.log (b + T + 6) ≤ D * B - T := by
  have hm := logarithmic_moment_cost_le hb hbT hT
  have htime := mul_le_mul_of_nonneg_left ht hD
  have hT0 : 0 ≤ T := by linarith only [hT]
  have he := mul_le_mul_of_nonneg_right hE hT0
  have hE0 : 0 ≤ Real.log (T + 2) := by linarith only [hE, hD]
  nlinarith only [hm, htime, he, mul_nonneg hE0 hT0]

#print axioms logarithmic_chernoff_exponent_le

/-- Logarithmic moment growth gives exponentially small leakage from a fixed
logarithmic window. The parameter `b` allows a fixed exponential tilt. -/
theorem positive_kernel_logarithmic_floor {F k : ℝ → ℝ} {A C b D K T B t : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hb : 0 ≤ b) (hbT : b ≤ T)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hT : 6 ≤ T)
    (hE : D + 1 ≤ Real.log (T + 2)) (ht : |t| ≤ T + B)
    (hk : ∀ x, 0 ≤ k x) (hki : Integrable k)
    (hkm : Integrable fun x => Real.exp ((D + T) * |x|) * k x)
    (hFi : Integrable fun x => k x * F (t + x))
    (hF : ∀ u, |F u| ≤ A * Real.exp (D * |u|))
    (hmoment : (∫ x, Real.exp ((D + T) * |x|) * k x) ≤
      C * Real.exp ((b + T + 6) * Real.log (b + T + 6)))
    (hlocal : ∀ x, |x| ≤ 8 * Real.log (T + 2) → -K ≤ F (t + x)) :
    -K * (∫ x, k x) - A * C * Real.exp (D * B - T) ≤
      ∫ x, k x * F (t + x) := by
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hf := positive_kernel_local_floor hA hD hK hT0 hk hki hkm hFi hF hlocal
  have hle : A * Real.exp (D * |t| - T * (8 * Real.log (T + 2))) *
      (∫ x, Real.exp ((D + T) * |x|) * k x) ≤ A * C * Real.exp (D * B - T) := by
    calc
      _ ≤ A * Real.exp (D * |t| - T * (8 * Real.log (T + 2))) *
          (C * Real.exp ((b + T + 6) * Real.log (b + T + 6))) :=
        mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ = A * C * Real.exp (D * |t| - T * (8 * Real.log (T + 2)) +
          (b + T + 6) * Real.log (b + T + 6)) := by rw [Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (logarithmic_chernoff_exponent_le hb hbT hD hT hE ht))
        (mul_nonneg hA hC)
  linarith only [hf, hle]

#print axioms positive_kernel_logarithmic_floor
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
