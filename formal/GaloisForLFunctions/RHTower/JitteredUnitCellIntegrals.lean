import GaloisForLFunctions.RHTower.JitteredCellWeilTerms

/-!
# Unit cells: exact integrals of the critical-line wave

For cells of length one, `[k+1, k+2)`, the cell term is `unitTerm k v t = wave t (k+1+v) − m_k(t)`
with `m_k(t) = ∫_{k+1}^{k+2} wave t` (`unitTerm_eq_cellTerm`).  Three antiderivatives give the
moments needed for the second-moment method:

* `integral_wave_sq`: `∫_a^b wave_t² = ½ log(b/a) + (sin(2t log b) − sin(2t log a))/(4t)`, because
  `d/dx [½ log x + sin(2t log x)/(4t)] = cos²(t log x)/x`;
* `abs_integral_wave_mul_le`: `|∫_a^b wave_t wave_{t'}| ≤ 1/|t−t'| + 1/|t+t'|`, from
  `d/dx ½[sin((t−t') log x)/(t−t') + sin((t+t') log x)/(t+t')] = cos(t log x) cos(t' log x)/x`;
* `abs_integral_wave_le`: `|∫_a^b wave_t| ≤ 2(√a + √b)/|t|`, from the antiderivative
  `√x (2 cos(t log x) + 4t sin(t log x))/(1 + 4t²)` of `wave_t`.
-/

open Real MeasureTheory Set

noncomputable section

namespace RHTower
namespace RandomCellWeil

/-- The term of a unit cell `[k+1, k+2)` with its atom at `k + 1 + v`. -/
def unitTerm (k : ℕ) (v t : ℝ) : ℝ :=
  wave t ((k : ℝ) + 1 + v) - ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), wave t x

theorem cellLeft_one (k : ℕ) : cellLeft 1 k = (k : ℝ) + 1 := by
  unfold cellLeft; push_cast; ring

theorem unitTerm_eq_cellTerm (k : ℕ) (v t : ℝ) : unitTerm k v t = cellTerm 1 k v t := by
  unfold unitTerm cellTerm
  rw [cellLeft_one]
  simp only [Nat.cast_one, inv_one, one_mul, div_one]
  congr 2
  ring

theorem wave_sq_le (t : ℝ) {x : ℝ} (hx : 0 < x) : wave t x ^ 2 ≤ 1 / x := by
  unfold wave
  rw [div_pow, Real.sq_sqrt hx.le]
  exact div_le_div_of_nonneg_right (by nlinarith [Real.cos_sq_le_one (t * Real.log x)]) hx.le

theorem wave_sq_eq (t : ℝ) {x : ℝ} (hx : 0 < x) :
    wave t x ^ 2 = Real.cos (t * Real.log x) ^ 2 / x := by
  unfold wave
  rw [div_pow, Real.sq_sqrt hx.le]

/-! ### The antiderivative of `wave²` -/

/-- `½ log x + sin(2t log x)/(4t)`. -/
def waveSqPrim (t x : ℝ) : ℝ := (1 / 2) * Real.log x + Real.sin (2 * t * Real.log x) / (4 * t)

theorem hasDerivAt_waveSqPrim {t : ℝ} (ht : t ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (waveSqPrim t) (wave t x ^ 2) x := by
  have h1 : HasDerivAt (fun y => (1 / 2 : ℝ) * Real.log y) ((1 / 2) * x⁻¹) x :=
    (Real.hasDerivAt_log hx.ne').const_mul _
  have h2 : HasDerivAt (fun y => Real.sin (2 * t * Real.log y))
      (Real.cos (2 * t * Real.log x) * (2 * t * x⁻¹)) x :=
    ((Real.hasDerivAt_log hx.ne').const_mul (2 * t)).sin
  have h3 : HasDerivAt (waveSqPrim t)
      ((1 / 2) * x⁻¹ + Real.cos (2 * t * Real.log x) * (2 * t * x⁻¹) / (4 * t)) x :=
    h1.add (h2.div_const (4 * t))
  refine h3.congr_deriv ?_
  rw [wave_sq_eq t hx, Real.cos_sq]
  rw [show 2 * t * Real.log x = 2 * (t * Real.log x) by ring]
  field_simp
  ring

theorem integral_wave_sq {t : ℝ} (ht : t ≠ 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, wave t x ^ 2 = waveSqPrim t b - waveSqPrim t a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact hasDerivAt_waveSqPrim ht (lt_of_lt_of_le ha hx.1)
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.pow
    apply (continuousOn_wave t).mono
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact lt_of_lt_of_le ha hx.1

theorem abs_sin_div_le (t y : ℝ) : |Real.sin y / (4 * t)| ≤ 1 / (4 * |t|) := by
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  rcases eq_or_ne t 0 with h | h
  · simp [h]
  · exact div_le_div_of_nonneg_right (Real.abs_sin_le_one y) (by positivity)

/-! ### The antiderivative of `wave_t · wave_{t'}` -/

/-- `½ [sin((t−t') log x)/(t−t') + sin((t+t') log x)/(t+t')]`. -/
def waveProdPrim (t t' x : ℝ) : ℝ :=
  (1 / 2) * (Real.sin ((t - t') * Real.log x) / (t - t')
    + Real.sin ((t + t') * Real.log x) / (t + t'))

theorem hasDerivAt_waveProdPrim {t t' : ℝ} (hd : t - t' ≠ 0) (hs : t + t' ≠ 0) {x : ℝ}
    (hx : 0 < x) : HasDerivAt (waveProdPrim t t') (wave t x * wave t' x) x := by
  have h1 : HasDerivAt (fun y => Real.sin ((t - t') * Real.log y))
      (Real.cos ((t - t') * Real.log x) * ((t - t') * x⁻¹)) x :=
    ((Real.hasDerivAt_log hx.ne').const_mul (t - t')).sin
  have h2 : HasDerivAt (fun y => Real.sin ((t + t') * Real.log y))
      (Real.cos ((t + t') * Real.log x) * ((t + t') * x⁻¹)) x :=
    ((Real.hasDerivAt_log hx.ne').const_mul (t + t')).sin
  have h3 : HasDerivAt (waveProdPrim t t')
      ((1 / 2 : ℝ) * (Real.cos ((t - t') * Real.log x) * ((t - t') * x⁻¹) / (t - t')
        + Real.cos ((t + t') * Real.log x) * ((t + t') * x⁻¹) / (t + t'))) x :=
    ((h1.div_const (t - t')).add (h2.div_const (t + t'))).const_mul (1 / 2 : ℝ)
  refine h3.congr_deriv ?_
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hs0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  unfold wave
  rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
  field_simp
  rw [Real.sq_sqrt hx.le]
  ring

theorem integral_wave_mul {t t' : ℝ} (hd : t - t' ≠ 0) (hs : t + t' ≠ 0) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    ∫ x in a..b, wave t x * wave t' x = waveProdPrim t t' b - waveProdPrim t t' a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact hasDerivAt_waveProdPrim hd hs (lt_of_lt_of_le ha hx.1)
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul <;> apply (continuousOn_wave _).mono <;> intro x hx <;>
      rw [uIcc_of_le hab] at hx <;> exact lt_of_lt_of_le ha hx.1

theorem abs_waveProdPrim_le (t t' x : ℝ) :
    |waveProdPrim t t' x| ≤ (1 / 2) * (1 / |t - t'| + 1 / |t + t'|) := by
  unfold waveProdPrim
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;>
  · rw [abs_div]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)

theorem abs_integral_wave_mul_le {t t' : ℝ} (hd : t - t' ≠ 0) (hs : t + t' ≠ 0) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    |∫ x in a..b, wave t x * wave t' x| ≤ 1 / |t - t'| + 1 / |t + t'| := by
  rw [integral_wave_mul hd hs ha hab]
  have h1 := abs_waveProdPrim_le t t' b
  have h2 := abs_waveProdPrim_le t t' a
  calc |waveProdPrim t t' b - waveProdPrim t t' a|
      ≤ |waveProdPrim t t' b| + |waveProdPrim t t' a| := abs_sub _ _
    _ ≤ _ := by linarith

/-! ### The antiderivative of `wave_t` -/

/-- `√x (2 cos(t log x) + 4t sin(t log x))/(1 + 4t²)`. -/
def wavePrim (t x : ℝ) : ℝ :=
  Real.sqrt x * (2 * Real.cos (t * Real.log x) + 4 * t * Real.sin (t * Real.log x)) / (1 + 4 * t ^ 2)

theorem hasDerivAt_wavePrim (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (wavePrim t) (wave t x) x := by
  have hc : HasDerivAt (fun y => Real.cos (t * Real.log y))
      (-Real.sin (t * Real.log x) * (t * x⁻¹)) x :=
    ((Real.hasDerivAt_log hx.ne').const_mul t).cos
  have hs : HasDerivAt (fun y => Real.sin (t * Real.log y))
      (Real.cos (t * Real.log x) * (t * x⁻¹)) x :=
    ((Real.hasDerivAt_log hx.ne').const_mul t).sin
  have hq := Real.hasDerivAt_sqrt hx.ne'
  have h : HasDerivAt (wavePrim t)
      ((1 / (2 * Real.sqrt x) * (2 * Real.cos (t * Real.log x) + 4 * t * Real.sin (t * Real.log x))
        + Real.sqrt x * (2 * (-Real.sin (t * Real.log x) * (t * x⁻¹))
          + 4 * t * (Real.cos (t * Real.log x) * (t * x⁻¹)))) / (1 + 4 * t ^ 2)) x :=
    (hq.mul ((hc.const_mul 2).add (hs.const_mul (4 * t)))).div_const (1 + 4 * t ^ 2)
  refine h.congr_deriv ?_
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hs0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hd : (1 + 4 * t ^ 2) ≠ 0 := by positivity
  unfold wave
  set L := t * Real.log x
  set y := Real.sqrt x with hy
  have hyx : x = y ^ 2 := (Real.sq_sqrt hx.le).symm
  rw [hyx]
  field_simp
  ring

theorem abs_wavePrim_le {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    |wavePrim t x| ≤ 2 * Real.sqrt x / |t| := by
  unfold wavePrim
  have hpos : (0 : ℝ) < 1 + 4 * t ^ 2 := by positivity
  have htabs : 0 < |t| := abs_pos.mpr ht
  rw [abs_div, abs_of_pos hpos, abs_mul, abs_of_nonneg (Real.sqrt_nonneg x)]
  have hinner : |2 * Real.cos (t * Real.log x) + 4 * t * Real.sin (t * Real.log x)|
      ≤ 2 + 4 * |t| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have h1 := Real.abs_cos_le_one (t * Real.log x)
    have h2 := Real.abs_sin_le_one (t * Real.log x)
    nlinarith [abs_nonneg t]
  rw [div_le_div_iff₀ hpos htabs]
  have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  calc Real.sqrt x * |2 * Real.cos (t * Real.log x) + 4 * t * Real.sin (t * Real.log x)| * |t|
      ≤ Real.sqrt x * (2 + 4 * |t|) * |t| := by
        apply mul_le_mul_of_nonneg_right _ htabs.le
        exact mul_le_mul_of_nonneg_left hinner (Real.sqrt_nonneg x)
    _ ≤ 2 * Real.sqrt x * (1 + 4 * t ^ 2) := by
        rw [hsq]
        have := Real.sqrt_nonneg x
        nlinarith [sq_nonneg (2 * |t| - 1)]

theorem abs_integral_wave_le {t : ℝ} (ht : t ≠ 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |∫ x in a..b, wave t x| ≤ 2 * (Real.sqrt a + Real.sqrt b) / |t| := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := wavePrim t)]
  · have h1 := abs_wavePrim_le ht b
    have h2 := abs_wavePrim_le ht a
    calc |wavePrim t b - wavePrim t a| ≤ |wavePrim t b| + |wavePrim t a| := abs_sub _ _
      _ ≤ 2 * Real.sqrt b / |t| + 2 * Real.sqrt a / |t| := add_le_add h1 h2
      _ = _ := by ring
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact hasDerivAt_wavePrim t (lt_of_lt_of_le ha hx.1)
  · apply ContinuousOn.intervalIntegrable
    apply (continuousOn_wave t).mono
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact lt_of_lt_of_le ha hx.1

/-! ### Adjacent unit cells -/

theorem intervalIntegrable_unit_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    (k : ℕ) : IntervalIntegrable f volume ((k : ℝ) + 1) ((k : ℝ) + 2) := by
  apply ContinuousOn.intervalIntegrable
  apply hf.mono
  intro x hx
  rw [uIcc_of_le (by linarith)] at hx
  simp only [mem_Ioi]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith [hx.1]

/-- `Σ_{k<K} ∫_{k+1}^{k+2} f = ∫_1^{K+1} f`. -/
theorem sum_integral_unit_cells {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0)) (K : ℕ) :
    ∑ k ∈ Finset.range K, ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), f x
      = ∫ x in (1 : ℝ)..((K : ℝ) + 1), f x := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
    (a := fun k : ℕ => (k : ℝ) + 1) (n := K) (by
      intro k _
      have := intervalIntegrable_unit_of_continuousOn hf k
      simpa [show ((k : ℝ) + 1 + 1) = (k : ℝ) + 2 by ring] using this)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  ring

end RandomCellWeil
end RHTower
