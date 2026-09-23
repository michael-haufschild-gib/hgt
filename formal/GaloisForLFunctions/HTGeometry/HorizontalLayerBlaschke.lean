import Mathlib

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

def horizontalLayerFactorRaw (a ω x : ℝ) : ℂ :=
  ((((x : ℝ) : ℂ) - ((a + ω : ℝ) : ℂ) * I) /
      (((x : ℝ) : ℂ) + ((a + ω : ℝ) : ℂ) * I)) *
    ((((x : ℝ) : ℂ) + ((a - ω : ℝ) : ℂ) * I) /
      (((x : ℝ) : ℂ) - ((a - ω : ℝ) : ℂ) * I))

def horizontalLayerFullInfinitesimalSymbol (a x : ℝ) : ℂ :=
  (-2 * I) / (((x : ℝ) : ℂ) - (a : ℂ) * I) +
    (-2 * I) / (((x : ℝ) : ℂ) + (a : ℂ) * I)

def horizontalLayerDenominator (a ω x : ℝ) : ℂ :=
  (((x : ℝ) : ℂ) + ((a + ω : ℝ) : ℂ) * I) *
    (((x : ℝ) : ℂ) - ((a - ω : ℝ) : ℂ) * I)

lemma real_add_mul_I_ne_zero {x r : ℝ} (hr : r ≠ 0) :
    ((x : ℂ) + (r : ℂ) * I) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  exact hr hi

lemma real_sub_mul_I_ne_zero {x r : ℝ} (hr : r ≠ 0) :
    ((x : ℂ) - (r : ℂ) * I) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  exact hr hi

theorem horizontalLayerFactorRaw_zero {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    horizontalLayerFactorRaw a 0 x = 1 := by
  have hp := real_add_mul_I_ne_zero (x := x) ha
  have hm := real_sub_mul_I_ne_zero (x := x) ha
  rw [horizontalLayerFactorRaw]
  norm_num
  field_simp

theorem horizontalLayerFactorRaw_normalized {a ω : ℝ}
    (hω : ω ≠ 0) (hplus : a + ω ≠ 0) (hminus : a - ω ≠ 0) (x : ℝ) :
    (horizontalLayerFactorRaw a ω x - 1) / (ω : ℂ) =
      (-4 * I * (x : ℂ)) / horizontalLayerDenominator a ω x := by
  have hp := real_add_mul_I_ne_zero (x := x) hplus
  have hm := real_sub_mul_I_ne_zero (x := x) hminus
  have hp' : ((x : ℂ) + I * ((a + ω : ℝ) : ℂ)) ≠ 0 := by
    convert hp using 1
    all_goals ring
  have hm' : ((x : ℂ) - I * ((a - ω : ℝ) : ℂ)) ≠ 0 := by
    convert hm using 1
    all_goals ring
  have hω' : (ω : ℂ) ≠ 0 := ofReal_ne_zero.mpr hω
  rw [horizontalLayerFactorRaw]
  unfold horizontalLayerDenominator
  field_simp [hp', hm', hω']
  push_cast
  ring

theorem horizontalLayerFullInfinitesimalSymbol_eq {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    horizontalLayerFullInfinitesimalSymbol a x =
      (-4 * I * (x : ℂ)) / horizontalLayerDenominator a 0 x := by
  have hp := real_add_mul_I_ne_zero (x := x) ha
  have hm := real_sub_mul_I_ne_zero (x := x) ha
  have hp' : ((x : ℂ) + I * (a : ℂ)) ≠ 0 := by
    convert hp using 1
    all_goals ring
  have hm' : ((x : ℂ) - I * (a : ℂ)) ≠ 0 := by
    convert hm using 1
    all_goals ring
  rw [horizontalLayerFullInfinitesimalSymbol]
  unfold horizontalLayerDenominator
  norm_num
  field_simp [hp', hm']
  ring

theorem horizontalLayerFactorRaw_normalized_sub {a ω : ℝ} (ha : a ≠ 0)
    (hω : ω ≠ 0) (hplus : a + ω ≠ 0) (hminus : a - ω ≠ 0) (x : ℝ) :
    (horizontalLayerFactorRaw a ω x - 1) / (ω : ℂ) -
        horizontalLayerFullInfinitesimalSymbol a x =
      (-4 * I * (x : ℂ)) *
        (((ω : ℂ) ^ (2 : ℕ) - 2 * I * (ω : ℂ) * (x : ℂ)) /
          (horizontalLayerDenominator a ω x * horizontalLayerDenominator a 0 x)) := by
  rw [horizontalLayerFactorRaw_normalized hω hplus hminus,
    horizontalLayerFullInfinitesimalSymbol_eq ha]
  have hpω := real_add_mul_I_ne_zero (x := x) hplus
  have hmω := real_sub_mul_I_ne_zero (x := x) hminus
  have hp := real_add_mul_I_ne_zero (x := x) ha
  have hm := real_sub_mul_I_ne_zero (x := x) ha
  have hDω : horizontalLayerDenominator a ω x ≠ 0 := by
    exact mul_ne_zero hpω hmω
  have hD0 : horizontalLayerDenominator a 0 x ≠ 0 := by
    unfold horizontalLayerDenominator
    norm_num
    exact ⟨hp, hm⟩
  field_simp [hDω, hD0]
  unfold horizontalLayerDenominator
  norm_num
  ring_nf
  rw [Complex.I_sq]
  ring

theorem norm_horizontalLayerDenominator_zero (a x : ℝ) :
    ‖horizontalLayerDenominator a 0 x‖ = x ^ (2 : ℕ) + a ^ (2 : ℕ) := by
  have hmul :
      (((x : ℂ) + (a : ℂ) * I) * ((x : ℂ) - (a : ℂ) * I)) =
        ((x ^ (2 : ℕ) + a ^ (2 : ℕ) : ℝ) : ℂ) := by
    calc
      ((x : ℂ) + (a : ℂ) * I) * ((x : ℂ) - (a : ℂ) * I) =
          (x : ℂ) ^ (2 : ℕ) - ((a : ℂ) * I) ^ (2 : ℕ) := by ring
      _ = ((x ^ (2 : ℕ) + a ^ (2 : ℕ) : ℝ) : ℂ) := by
        rw [mul_pow, Complex.I_sq]
        push_cast
        ring
  unfold horizontalLayerDenominator
  norm_num
  rw [← norm_mul, hmul, norm_real, Real.norm_eq_abs, abs_of_nonneg]
  positivity

theorem norm_horizontalLayerDenominator_lower {a ω : ℝ} (ha : 0 < a)
    (hsmall : |ω| ≤ a / 2) (x : ℝ) :
    a ^ (2 : ℕ) / 4 ≤ ‖horizontalLayerDenominator a ω x‖ := by
  have hω := (abs_le.mp hsmall)
  have hplus : a / 2 ≤ a + ω := by linarith
  have hminus : a / 2 ≤ a - ω := by linarith
  have hplus0 : 0 ≤ a + ω := le_trans (by linarith) hplus
  have hminus0 : 0 ≤ a - ω := le_trans (by linarith) hminus
  have hp : a / 2 ≤ ‖(x : ℂ) + (a + ω : ℂ) * I‖ := by
    calc
      a / 2 ≤ |a + ω| := by rw [abs_of_nonneg hplus0]; exact hplus
      _ ≤ ‖(x : ℂ) + (a + ω : ℂ) * I‖ := by
        have h := Complex.abs_im_le_norm ((x : ℂ) + (a + ω : ℂ) * I)
        simpa using h
  have hm : a / 2 ≤ ‖(x : ℂ) - (a - ω : ℂ) * I‖ := by
    calc
      a / 2 ≤ |-(a - ω)| := by rw [abs_neg, abs_of_nonneg hminus0]; exact hminus
      _ ≤ ‖(x : ℂ) - (a - ω : ℂ) * I‖ := by
        have h := Complex.abs_im_le_norm ((x : ℂ) - (a - ω : ℂ) * I)
        simpa using h
  rw [horizontalLayerDenominator, norm_mul]
  push_cast
  calc
    a ^ (2 : ℕ) / 4 = (a / 2) * (a / 2) := by ring
    _ ≤ ‖(x : ℂ) + (a + ω : ℂ) * I‖ *
        ‖(x : ℂ) - (a - ω : ℂ) * I‖ :=
      mul_le_mul hp hm (by linarith) (norm_nonneg _)

theorem norm_horizontalLayerRemainderNumerator_le (ω x : ℝ) :
    ‖(ω : ℂ) ^ (2 : ℕ) - 2 * I * (ω : ℂ) * (x : ℂ)‖ ≤
      |ω| * (|ω| + 2 * |x|) := by
  calc
    ‖(ω : ℂ) ^ (2 : ℕ) - 2 * I * (ω : ℂ) * (x : ℂ)‖ ≤
        ‖(ω : ℂ) ^ (2 : ℕ)‖ + ‖2 * I * (ω : ℂ) * (x : ℂ)‖ := norm_sub_le _ _
    _ = |ω| * (|ω| + 2 * |x|) := by
      simp only [norm_pow, norm_real, norm_mul, norm_ofNat, norm_I, Real.norm_eq_abs]
      ring

lemma abs_mul_horizontalLayerRemainder_le {a ω : ℝ} (ha : 0 < a)
    (hsmall : |ω| ≤ a / 2) (x : ℝ) :
    |x| * (|ω| + 2 * |x|) ≤ 3 * (x ^ (2 : ℕ) + a ^ (2 : ℕ)) := by
  have hωa : |ω| ≤ a := hsmall.trans (by linarith)
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hω0 : 0 ≤ |ω| := abs_nonneg ω
  have hxa := sq_nonneg (|x| - a)
  nlinarith [sq_abs x]

theorem norm_horizontalLayerFactorRaw_normalized_sub_le {a ω : ℝ} (ha : 0 < a)
    (hω : ω ≠ 0) (hsmall : |ω| ≤ a / 2) (x : ℝ) :
    ‖(horizontalLayerFactorRaw a ω x - 1) / (ω : ℂ) -
        horizontalLayerFullInfinitesimalSymbol a x‖ ≤
      48 * |ω| / a ^ (2 : ℕ) := by
  have hωbounds := abs_le.mp hsmall
  have hplus : 0 < a + ω := by linarith
  have hminus : 0 < a - ω := by linarith
  have hDω := norm_horizontalLayerDenominator_lower ha hsmall x
  have hDωpos : 0 < ‖horizontalLayerDenominator a ω x‖ :=
    lt_of_lt_of_le (by positivity : 0 < a ^ (2 : ℕ) / 4) hDω
  have hSpos : 0 < x ^ (2 : ℕ) + a ^ (2 : ℕ) := by nlinarith [sq_nonneg x, sq_pos_of_pos ha]
  have hD0pos : 0 < ‖horizontalLayerDenominator a 0 x‖ := by
    rw [norm_horizontalLayerDenominator_zero]
    exact hSpos
  have hdenpos :
      0 < ‖horizontalLayerDenominator a ω x * horizontalLayerDenominator a 0 x‖ := by
    rw [norm_mul]
    positivity
  have hden :
      (a ^ (2 : ℕ) / 4) * (x ^ (2 : ℕ) + a ^ (2 : ℕ)) ≤
        ‖horizontalLayerDenominator a ω x * horizontalLayerDenominator a 0 x‖ := by
    rw [norm_mul, norm_horizontalLayerDenominator_zero]
    exact mul_le_mul_of_nonneg_right hDω (le_of_lt hSpos)
  have hnum := norm_horizontalLayerRemainderNumerator_le ω x
  have hreal := abs_mul_horizontalLayerRemainder_le ha hsmall x
  have htop :
      4 * |x| * ‖(ω : ℂ) ^ (2 : ℕ) - 2 * I * (ω : ℂ) * (x : ℂ)‖ ≤
        12 * |ω| * (x ^ (2 : ℕ) + a ^ (2 : ℕ)) := by
    calc
      4 * |x| * ‖(ω : ℂ) ^ (2 : ℕ) - 2 * I * (ω : ℂ) * (x : ℂ)‖ ≤
          4 * |x| * (|ω| * (|ω| + 2 * |x|)) := by gcongr
      _ ≤ 12 * |ω| * (x ^ (2 : ℕ) + a ^ (2 : ℕ)) := by
        have h := mul_le_mul_of_nonneg_left hreal
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (abs_nonneg ω))
        nlinarith
  rw [horizontalLayerFactorRaw_normalized_sub ha.ne' hω hplus.ne' hminus.ne']
  calc
    ‖(-4 * I * (x : ℂ)) *
        (((ω : ℂ) ^ (2 : ℕ) - 2 * I * (ω : ℂ) * (x : ℂ)) /
          (horizontalLayerDenominator a ω x * horizontalLayerDenominator a 0 x))‖ =
        (4 * |x| * ‖(ω : ℂ) ^ (2 : ℕ) - 2 * I * (ω : ℂ) * (x : ℂ)‖) /
          ‖horizontalLayerDenominator a ω x * horizontalLayerDenominator a 0 x‖ := by
      rw [norm_mul, norm_div]
      simp only [norm_neg, norm_mul, norm_ofNat, norm_I, norm_real, Real.norm_eq_abs]
      ring
    _ ≤ (12 * |ω| * (x ^ (2 : ℕ) + a ^ (2 : ℕ))) /
          ‖horizontalLayerDenominator a ω x * horizontalLayerDenominator a 0 x‖ := by
      exact (div_le_div_iff_of_pos_right hdenpos).2 htop
    _ ≤ (12 * |ω| * (x ^ (2 : ℕ) + a ^ (2 : ℕ))) /
          ((a ^ (2 : ℕ) / 4) * (x ^ (2 : ℕ) + a ^ (2 : ℕ))) := by
      gcongr
    _ = 48 * |ω| / a ^ (2 : ℕ) := by
      field_simp [ne_of_gt ha, ne_of_gt hSpos]
      ring

end GaloisForLFunctions.HTGeometry
