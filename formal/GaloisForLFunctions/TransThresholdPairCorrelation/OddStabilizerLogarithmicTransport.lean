import GaloisForLFunctions.TransThresholdPairCorrelation.CosineTransformLogarithmicTransport
import GaloisForLFunctions.TransThresholdPairCorrelation.OddStabilizerApertureBounds

/-!
# Finite logarithmic stabilizer rows with their spatial correction

The logarithmic phase and square-root pair weight transport to the linear
Poisson row with a summable Fourier-decay error. A cubic aperture tail leaves
the primitive spatial correction explicit. A first logarithmic moment controls
linear-taper variation, and positive-frequency mass bounds every finite row
uniformly in its base.
-/

noncomputable section
open MeasureTheory Real Filter Topology Finset
open Zeta23
namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- Explicit Fourier moments controlling the logarithmic phase and square-root
pair-weight errors at a reference height `T`. -/
def logarithmicTransportBound (Ω : ℝ → ℝ) (a b T : ℝ) : ℝ :=
  4 * ((∫ t in (a - 1)..(b + 1), |t * Ω t|) / T^2 +
    16 * T^2 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 (fun t => t * Ω t) t|)) +
  2 * ((∫ t in (a - 1)..(b + 1), |Ω t|) / T +
    T^3 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|))

private theorem two_scale_envelope {A D x y : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hx : 0 < x)
    (hhead : x ≤ 1 → y ≤ A) (htail : 1 ≤ x → y ≤ D / x^2) :
    y ≤ 4 * (A + D) / (1 + x)^2 := by
  have hden : 0 < (1 + x)^2 := by positivity
  by_cases hx1 : x ≤ 1
  · apply (hhead hx1).trans
    rw [le_div_iff₀ hden]
    have hx2 : x^2 ≤ 1 := pow_le_one₀ hx.le hx1
    have hb : (1 + x)^2 ≤ 4 := by nlinarith only [hx1, hx2]
    have hm := mul_le_mul_of_nonneg_left hb hA
    nlinarith only [hm, hD]
  · have h1 : 1 ≤ x := by linarith only [hx1]
    have hb : (1 + x)^2 ≤ 4 * x^2 := by nlinarith only [h1, sq_nonneg (x - 1)]
    apply (htail h1).trans
    rw [div_le_div_iff₀ (sq_pos_of_pos hx) hden]
    have hm := mul_le_mul_of_nonneg_left hb hD
    have ha2 := mul_nonneg hA (sq_nonneg x)
    nlinarith only [hm, ha2]

private theorem phase_difference_envelope {Ω : ℝ → ℝ} {a b T x : ℝ}
    (hab : a ≤ b) (hT : 0 < T) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) (hx : 0 < x) (hx1 : x ≤ 1) :
    |cosTransform Ω (Real.log (1 + x)) - cosTransform Ω x| ≤
      4 * ((∫ t in (a - 1)..(b + 1), |t * Ω t|) / T^2 +
        16 * T^2 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 (fun t => t * Ω t) t|)) /
          (1 + T * x)^2 := by
  let M := ∫ t in (a - 1)..(b + 1), |t * Ω t|
  let D := ∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 (fun t => t * Ω t) t|
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have h := abs_cosTransform_log_sub_linear_le hab hΩ hsupp hx hx1
  apply two_scale_envelope (div_nonneg hM (sq_nonneg T))
    (mul_nonneg (by positivity) hD) (mul_pos hT hx)
  · intro hsmall
    calc
      _ ≤ M * x^2 := h.trans (min_le_left _ _)
      _ = (M / T^2) * (T * x)^2 := by field_simp [hT.ne']
      _ ≤ (M / T^2) * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ (mul_pos hT hx).le hsmall) (div_nonneg hM (sq_nonneg T))
      _ = _ := mul_one _
  · intro _
    calc
      _ ≤ 16 * D / x^2 := h.trans (min_le_right _ _)
      _ = _ := by field_simp [hT.ne', hx.ne']

private theorem weighted_transform_envelope {Ω : ℝ → ℝ} {a b T x : ℝ}
    (hab : a ≤ b) (hT : 0 < T) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) (hx : 0 < x) :
    x * |cosTransform Ω x| ≤
      4 * ((∫ t in (a - 1)..(b + 1), |Ω t|) / T +
        T^3 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|)) / (1 + T * x)^2 := by
  let M := ∫ t in (a - 1)..(b + 1), |Ω t|
  let D := ∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have h0 := abs_cosTransform_le_mass hab hΩ.continuous hsupp x
  have h4 := abs_cosTransform_le hab hΩ hsupp hx.ne'
  rw [abs_of_pos hx] at h4
  apply two_scale_envelope (div_nonneg hM hT.le)
    (mul_nonneg (pow_nonneg hT.le _) hD) (mul_pos hT hx)
  · intro hsmall
    calc
      _ ≤ x * M := mul_le_mul_of_nonneg_left h0 hx.le
      _ = (M / T) * (T * x) := by field_simp [hT.ne']
      _ ≤ (M / T) * 1 := mul_le_mul_of_nonneg_left hsmall (div_nonneg hM hT.le)
      _ = _ := mul_one _
  · intro hlarge
    calc
      _ ≤ x * (D / x^4) := mul_le_mul_of_nonneg_left h4 hx.le
      _ = (T^3 * D) / (T * x)^3 := by field_simp [hT.ne', hx.ne']
      _ ≤ (T^3 * D) / (T * x)^2 := div_le_div_of_nonneg_left
        (mul_nonneg (pow_nonneg hT.le _) hD) (by positivity)
        (pow_le_pow_right₀ hlarge (by norm_num : (2 : ℕ) ≤ 3))


private theorem logarithmicTransportBound_nonneg {Ω : ℝ → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hT : 0 < T) : 0 ≤ logarithmicTransportBound Ω a b T := by
  have hi (f : ℝ → ℝ) : 0 ≤ ∫ t in (a - 1)..(b + 1), |f t| :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have h0 := hi Ω
  have h1 := hi (fun t => t * Ω t)
  have hd0 := hi (iteratedDeriv 4 Ω)
  have hd1 := hi (iteratedDeriv 4 (fun t => t * Ω t))
  unfold logarithmicTransportBound
  positivity

private theorem paired_kernel_error_envelope {Ω : ℝ → ℝ} {a b T m h : ℝ}
    (hab : a ≤ b) (hT : 0 < T) (hm : 0 < m) (hh : 0 < h) (hhm : h ≤ m)
    (hΩ : ContDiff ℝ 4 Ω) (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) :
    |cosTransform Ω (Real.log (1 + h / m)) / Real.sqrt (m * (m + h)) -
      cosTransform Ω (h / m) / m| ≤
      logarithmicTransportBound Ω a b T / (m * (1 + T * (h / m))^2) := by
  let S := Real.sqrt (m * (m + h))
  let F := cosTransform Ω
  let C1 := (∫ t in (a - 1)..(b + 1), |t * Ω t|) / T^2 +
    16 * T^2 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 (fun t => t * Ω t) t|)
  let C0 := (∫ t in (a - 1)..(b + 1), |Ω t|) / T +
    T^3 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|)
  have hx : 0 < h / m := div_pos hh hm
  have hx1 : h / m ≤ 1 := (div_le_one hm).mpr hhm
  have hSpos : 0 < S := Real.sqrt_pos.mpr (mul_pos hm (by linarith))
  have hmS : m ≤ S := by
    rw [← Real.sqrt_sq hm.le]
    exact Real.sqrt_le_sqrt (by nlinarith only [mul_nonneg hm.le hh.le])
  have hinv : 1 / S ≤ 1 / m := (one_div_le_one_div hSpos hm).mpr hmS
  have hweight := inv_sub_inv_sqrt_mul_bounds hm hh.le
  have hphase := phase_difference_envelope hab hT hΩ hsupp hx hx1
  have hfreq := weighted_transform_envelope hab hT hΩ hsupp hx
  have hsplit : F (Real.log (1 + h / m)) / S - F (h / m) / m =
      (1 / S) * (F (Real.log (1 + h / m)) - F (h / m)) -
        (1 / m - 1 / S) * F (h / m) := by ring
  change |F (Real.log (1 + h / m)) / S - F (h / m) / m| ≤ _
  rw [hsplit]
  have hp : |(1 / S) * (F (Real.log (1 + h / m)) - F (h / m))| ≤
      (1 / m) * (4 * C1 / (1 + T * (h / m))^2) := by
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hSpos)]
    exact mul_le_mul hinv hphase (abs_nonneg _) (by positivity)
  have hw : |(1 / m - 1 / S) * F (h / m)| ≤
      (1 / (2 * m)) * (4 * C0 / (1 + T * (h / m))^2) := by
    rw [abs_mul, abs_of_nonneg hweight.1]
    calc
      _ ≤ (h / (2 * m^2)) * |F (h / m)| :=
        mul_le_mul_of_nonneg_right hweight.2 (abs_nonneg _)
      _ = (1 / (2 * m)) * ((h / m) * |F (h / m)|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfreq (by positivity)
  calc
    _ ≤ |(1 / S) * (F (Real.log (1 + h / m)) - F (h / m))| +
        |(1 / m - 1 / S) * F (h / m)| := abs_sub _ _
    _ ≤ (1 / m) * (4 * C1 / (1 + T * (h / m))^2) +
        (1 / (2 * m)) * (4 * C0 / (1 + T * (h / m))^2) := add_le_add hp hw
    _ = _ := by
      change _ = (4 * C1 + 2 * C0) / (m * (1 + T * (h / m))^2)
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Finite positive even-shift row with the literal logarithmic phase and
square-root pair weight. -/
def stabilizerLogarithmicRow (Q : ℕ) (Ω : ℝ → ℝ) (m : ℝ) (R : ℕ) : ℝ :=
  ∑ n ∈ range R, parityStabilizerWeight Q (2 * (n + 1)) *
    cosTransform Ω (Real.log (1 + ((2 * (n + 1) : ℕ) : ℝ) / m)) /
      Real.sqrt (m * (m + ((2 * (n + 1) : ℕ) : ℝ)))

/-- Summing the decaying Fourier error controls logarithmic phase and
square-root weight together, uniformly over every aperture with `2R≤m`. -/
theorem abs_stabilizerLogarithmicRow_sub_linear_le {Ω : ℝ → ℝ} {a b T m : ℝ}
    (Q R : ℕ) (hab : a ≤ b) (hT : 0 < T) (hm : 0 < m)
    (hR : ((2 * R : ℕ) : ℝ) ≤ m) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) :
    |stabilizerLogarithmicRow Q Ω m R -
      (∑ n ∈ range R, parityStabilizerWeight Q (2 * (n + 1)) *
        cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m)) / m| ≤
      (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) *
        logarithmicTransportBound Ω a b T / T := by
  let O := ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q
  let C := logarithmicTransportBound Ω a b T
  have hO : 0 ≤ O := sum_nonneg (fun q _ => RHTower.Sieve.sqfreeTotientInv_nonneg q)
  have hC : 0 ≤ C := logarithmicTransportBound_nonneg hab hT
  have he : stabilizerLogarithmicRow Q Ω m R -
      (∑ n ∈ range R, parityStabilizerWeight Q (2 * (n + 1)) *
        cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m)) / m =
      ∑ n ∈ range R, parityStabilizerWeight Q (2 * (n + 1)) *
        (cosTransform Ω (Real.log (1 + ((2 * (n + 1) : ℕ) : ℝ) / m)) /
            Real.sqrt (m * (m + ((2 * (n + 1) : ℕ) : ℝ))) -
          cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m) / m) := by
    rw [stabilizerLogarithmicRow, sum_div, ← sum_sub_distrib]
    exact sum_congr rfl (fun n _ => by ring)
  rw [he]
  have hpt (n : ℕ) (hn : n ∈ range R) :
      |parityStabilizerWeight Q (2 * (n + 1)) *
        (cosTransform Ω (Real.log (1 + ((2 * (n + 1) : ℕ) : ℝ) / m)) /
            Real.sqrt (m * (m + ((2 * (n + 1) : ℕ) : ℝ))) -
          cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m) / m)| ≤
      (2 * O * C / m) * (1 / (1 + (2 * T / m) * ((n : ℝ) + 1))^2) := by
    have hnr : (2 * (n + 1) : ℕ) ≤ 2 * R := by
      have := mem_range.mp hn
      omega
    have hh : (0 : ℝ) < ((2 * (n + 1) : ℕ) : ℝ) := by positivity
    have hnrR : ((2 * (n + 1) : ℕ) : ℝ) ≤ ((2 * R : ℕ) : ℝ) := by exact_mod_cast hnr
    have hhm : ((2 * (n + 1) : ℕ) : ℝ) ≤ m := hnrR.trans hR
    have hk := paired_kernel_error_envelope hab hT hm hh hhm hΩ hsupp
    rw [abs_mul]
    calc
      _ ≤ (2 * O) * (C / (m * (1 + T * (((2 * (n + 1) : ℕ) : ℝ) / m))^2)) :=
        mul_le_mul (abs_parityStabilizerWeight_le Q _) hk (abs_nonneg _) (by positivity)
      _ = _ := by
        have hrw : T * (((2 * (n + 1) : ℕ) : ℝ) / m) =
            (2 * T / m) * ((n : ℝ) + 1) := by push_cast; ring
        rw [hrw]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  calc
    _ ≤ ∑ n ∈ range R, |parityStabilizerWeight Q (2 * (n + 1)) *
        (cosTransform Ω (Real.log (1 + ((2 * (n + 1) : ℕ) : ℝ) / m)) /
            Real.sqrt (m * (m + ((2 * (n + 1) : ℕ) : ℝ))) -
          cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m) / m)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range R, (2 * O * C / m) *
        (1 / (1 + (2 * T / m) * ((n : ℝ) + 1))^2) := sum_le_sum hpt
    _ = (2 * O * C / m) * ∑ n ∈ range R, 1 / (1 + (2 * T / m) * ((n : ℝ) + 1))^2 :=
      (mul_sum ..).symm
    _ ≤ (2 * O * C / m) * (1 / (2 * T / m)) :=
      mul_le_mul_of_nonneg_left (sum_inverse_square_affine_le (by positivity) R) (by positivity)
    _ = _ := by
      change (2 * O * C / m) * (1 / (2 * T / m)) = O * C / T
      field_simp [hm.ne', hT.ne']

/-- The finite logarithmic row retains the exact primitive spatial correction;
its error consists of phase and pair-weight transport plus a cubic aperture tail. -/
theorem abs_stabilizerLogarithmicRow_sub_dual_le {Ω : ℝ → ℝ} {a b T m : ℝ}
    (Q R : ℕ) (hab : a ≤ b) (hT : 0 < T) (hm : 0 < m)
    (hR : 1 ≤ R) (hRm : ((2 * R : ℕ) : ℝ) ≤ m) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) :
    |stabilizerLogarithmicRow Q Ω m R -
      (π * stabilizerSpatialDual Q Ω m - cosTransform Ω 0 *
        (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) / m)| ≤
      (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) *
        logarithmicTransportBound Ω a b T / T +
      (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) *
        (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|) * m^3 / (8 * (R : ℝ)^3) := by
  let P := ∑ n ∈ range R, parityStabilizerWeight Q (2 * (n + 1)) *
    cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m)
  let O := ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q
  let D := ∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|
  have hbdd : ∀ t, Ω t ≠ 0 → |t| ≤ max |a| |b| := by
    intro t ht
    have hmem : t ∈ Set.Icc a b := by
      by_contra hn
      exact ht (hsupp t hn)
    exact abs_le.mpr ⟨(neg_le_neg (le_max_left |a| |b|)).trans
      ((neg_abs_le a).trans hmem.1), hmem.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
  have hdual : stabilizerLinearRow Q Ω m / m =
      π * stabilizerSpatialDual Q Ω m - cosTransform Ω 0 * O / m := by
    rw [stabilizerLinearRow_eq_dual Q hm (hΩ.of_le (by norm_num)) hbdd]
    dsimp [O]
    field_simp [hm.ne']
  have htail : |P / m - stabilizerLinearRow Q Ω m / m| ≤
      O * D * m^3 / (8 * (R : ℝ)^3) := by
    rw [← sub_div, abs_div, abs_of_pos hm]
    calc
      _ ≤ (2 * O * D * (m / 2)^4 / (R : ℝ)^3) / m :=
        div_le_div_of_nonneg_right (abs_stabilizerLinearRow_truncation_le Q hab hm hΩ hsupp hR) hm.le
      _ = _ := by field_simp [hm.ne']; ring
  rw [← hdual]
  exact (abs_sub_le _ (P / m) _).trans
    (add_le_add (abs_stabilizerLogarithmicRow_sub_linear_le Q R hab hT hm hRm hΩ hsupp) htail)

private theorem logarithmic_moment_envelope {Ω : ℝ → ℝ} {a b T x : ℝ}
    (hab : a ≤ b) (hT : 0 < T) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log (1 + x) * |cosTransform Ω (Real.log (1 + x))| ≤
      4 * ((∫ t in (a - 1)..(b + 1), |Ω t|) / T +
        16 * T^3 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|)) / (1 + T * x)^2 := by
  let M := ∫ t in (a - 1)..(b + 1), |Ω t|
  let D := ∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have hl := log_one_add_div_bounds (m := 1) (h := x) (by norm_num) hx.le
  simp only [div_one] at hl
  have hhalf : x / 2 ≤ Real.log (1 + x) :=
    (div_le_div_of_nonneg_left hx.le (by positivity : 0 < 1 + x)
      (by linarith : 1 + x ≤ 2)).trans hl.1
  have hlp : 0 < Real.log (1 + x) := lt_of_lt_of_le (by positivity) hhalf
  have h0 := abs_cosTransform_le_mass hab hΩ.continuous hsupp (Real.log (1 + x))
  have h4 := abs_cosTransform_le hab hΩ hsupp hlp.ne'
  rw [abs_of_pos hlp] at h4
  have hdecay : Real.log (1 + x) * |cosTransform Ω (Real.log (1 + x))| ≤
      16 * D / x^3 := by
    calc
      _ ≤ x * (D / (x / 2)^4) := mul_le_mul hl.2
        (h4.trans (div_le_div_of_nonneg_left hD (by positivity)
          (pow_le_pow_left₀ (by positivity) hhalf 4))) (abs_nonneg _) hx.le
      _ = _ := by field_simp [hx.ne']; ring
  apply two_scale_envelope (div_nonneg hM hT.le)
    (mul_nonneg (by positivity) hD) (mul_pos hT hx)
  · intro hsmall
    calc
      _ ≤ x * M := mul_le_mul hl.2 h0 (abs_nonneg _) hx.le
      _ = (M / T) * (T * x) := by field_simp [hT.ne']
      _ ≤ (M / T) * 1 := mul_le_mul_of_nonneg_left hsmall (div_nonneg hM hT.le)
      _ = _ := mul_one _
  · intro hlarge
    calc
      _ ≤ 16 * D / x^3 := hdecay
      _ = (16 * T^3 * D) / (T * x)^3 := by field_simp [hT.ne', hx.ne']
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hlarge (by norm_num : (2 : ℕ) ≤ 3))

/-- The logarithmic first moment controls the variation of a linear taper
between the two endpoints of every coalescent pair. -/
theorem sum_abs_stabilizerLogarithmicMoment_le {Ω : ℝ → ℝ} {a b T m : ℝ}
    (Q R : ℕ) (hab : a ≤ b) (hT : 0 < T) (hm : 0 < m)
    (hR : ((2 * R : ℕ) : ℝ) ≤ m) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) :
    (∑ n ∈ range R, |parityStabilizerWeight Q (2 * (n + 1)) *
      Real.log (1 + ((2 * (n + 1) : ℕ) : ℝ) / m) *
      cosTransform Ω (Real.log (1 + ((2 * (n + 1) : ℕ) : ℝ) / m)) /
        Real.sqrt (m * (m + ((2 * (n + 1) : ℕ) : ℝ)))|) ≤
      4 * (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) *
        ((∫ t in (a - 1)..(b + 1), |Ω t|) / T +
          16 * T^3 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|)) / T := by
  let O := ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q
  let C := (∫ t in (a - 1)..(b + 1), |Ω t|) / T +
    16 * T^3 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|)
  have hO : 0 ≤ O := sum_nonneg (fun q _ => RHTower.Sieve.sqfreeTotientInv_nonneg q)
  have hC : 0 ≤ C := by
    have h0 : 0 ≤ ∫ t in (a - 1)..(b + 1), |Ω t| :=
      intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
    have hd : 0 ≤ ∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t| :=
      intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
    dsimp [C]
    positivity
  have hpt (n : ℕ) (hn : n ∈ range R) :
      |parityStabilizerWeight Q (2 * (n + 1)) *
        Real.log (1 + ((2 * (n + 1) : ℕ) : ℝ) / m) *
        cosTransform Ω (Real.log (1 + ((2 * (n + 1) : ℕ) : ℝ) / m)) /
          Real.sqrt (m * (m + ((2 * (n + 1) : ℕ) : ℝ)))| ≤
      (8 * O * C / m) * (1 / (1 + (2 * T / m) * ((n : ℝ) + 1))^2) := by
    let h : ℝ := ((2 * (n + 1) : ℕ) : ℝ)
    have hh : 0 < h := by dsimp [h]; positivity
    have hhm : h ≤ m := by
      have hnR : (2 * (n + 1) : ℕ) ≤ 2 * R := by have := mem_range.mp hn; omega
      have hcast : h ≤ ((2 * R : ℕ) : ℝ) := by dsimp [h]; exact_mod_cast hnR
      exact hcast.trans hR
    have hx : 0 < h / m := div_pos hh hm
    have hlog : 0 < Real.log (1 + h / m) := Real.log_pos (by linarith)
    have hS : 0 < Real.sqrt (m * (m + h)) := Real.sqrt_pos.mpr (by positivity)
    have hmS : m ≤ Real.sqrt (m * (m + h)) := by
      calc
        m = Real.sqrt (m^2) := (Real.sqrt_sq hm.le).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith only [mul_nonneg hm.le hh.le])
    have he := logarithmic_moment_envelope hab hT hΩ hsupp hx ((div_le_one hm).mpr hhm)
    change |parityStabilizerWeight Q (2 * (n + 1)) * Real.log (1 + h / m) *
      cosTransform Ω (Real.log (1 + h / m)) / Real.sqrt (m * (m + h))| ≤ _
    rw [abs_div, abs_of_pos hS, abs_mul, abs_mul, abs_of_pos hlog, mul_assoc]
    calc
      _ ≤ (2 * O) * (4 * C / (1 + T * (h / m))^2) / Real.sqrt (m * (m + h)) :=
        div_le_div_of_nonneg_right (mul_le_mul (abs_parityStabilizerWeight_le Q _) he
          (mul_nonneg hlog.le (abs_nonneg _)) (by positivity)) hS.le
      _ ≤ (2 * O) * (4 * C / (1 + T * (h / m))^2) / m :=
        div_le_div_of_nonneg_left (by positivity) hm hmS
      _ = _ := by
        have hrw : T * (h / m) = (2 * T / m) * ((n : ℝ) + 1) := by dsimp [h]; push_cast; ring
        rw [hrw]
        simp only [div_eq_mul_inv]
        ring
  calc
    _ ≤ ∑ n ∈ range R, (8 * O * C / m) *
        (1 / (1 + (2 * T / m) * ((n : ℝ) + 1))^2) := sum_le_sum hpt
    _ = (8 * O * C / m) * ∑ n ∈ range R, 1 / (1 + (2 * T / m) * ((n : ℝ) + 1))^2 :=
      (mul_sum ..).symm
    _ ≤ (8 * O * C / m) * (1 / (2 * T / m)) :=
      mul_le_mul_of_nonneg_left (sum_inverse_square_affine_le (by positivity) R) (by positivity)
    _ = _ := by
      change (8 * O * C / m) * (1 / (2 * T / m)) = 4 * O * C / T
      field_simp [hm.ne', hT.ne']; ring

/-- Every finite logarithmic row has a uniform base-scale envelope. Positive
Fourier lattice mass avoids an additive height loss on short rows. -/
theorem abs_stabilizerLogarithmicRow_le {Ω : ℝ → ℝ} {a b T m : ℝ}
    (Q R : ℕ) (hab : a ≤ b) (hT : 0 < T) (hm : 0 < m)
    (hR : ((2 * R : ℕ) : ℝ) ≤ m) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) :
    |stabilizerLogarithmicRow Q Ω m R| ≤
      (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) *
        (4 * ((∫ t in (a - 1)..(b + 1), |Ω t|) / T +
          T^3 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|)) +
            logarithmicTransportBound Ω a b T / T) := by
  let P := ∑ n ∈ range R, parityStabilizerWeight Q (2 * (n + 1)) *
    cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m)
  let O := ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q
  let C0 := (∫ t in (a - 1)..(b + 1), |Ω t|) / T +
    T^3 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|)
  have hO : 0 ≤ O := sum_nonneg (fun q _ => RHTower.Sieve.sqfreeTotientInv_nonneg q)
  have hP : |P| ≤ 4 * m * O * C0 := by
    calc
      _ ≤ ∑ n ∈ range R, |parityStabilizerWeight Q (2 * (n + 1)) *
          cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ range R, (2 * O) * |cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m)| := by
        refine sum_le_sum fun n _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_parityStabilizerWeight_le Q _) (abs_nonneg _)
      _ = (2 * O) * ∑ n ∈ range R, |cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m)| :=
        (mul_sum ..).symm
      _ ≤ (2 * O) * (2 * m * C0) := mul_le_mul_of_nonneg_left
        (sum_abs_cosTransform_even_lattice_le hab hT hm hΩ hsupp R) (by positivity)
      _ = _ := by ring
  have hdiv : |P / m| ≤ 4 * O * C0 := by
    rw [abs_div, abs_of_pos hm]
    calc
      _ ≤ (4 * m * O * C0) / m := div_le_div_of_nonneg_right hP hm.le
      _ = _ := by field_simp [hm.ne']
  have he := abs_stabilizerLogarithmicRow_sub_linear_le Q R hab hT hm hR hΩ hsupp
  calc
    _ = |(stabilizerLogarithmicRow Q Ω m R - P / m) + P / m| := by ring_nf
    _ ≤ |stabilizerLogarithmicRow Q Ω m R - P / m| + |P / m| := abs_add_le _ _
    _ ≤ O * logarithmicTransportBound Ω a b T / T + 4 * O * C0 := add_le_add he hdiv
    _ = _ := by
      change O * logarithmicTransportBound Ω a b T / T + 4 * O * C0 =
        O * (4 * C0 + logarithmicTransportBound Ω a b T / T)
      ring

end GaloisForLFunctions.TransThresholdPairCorrelation
