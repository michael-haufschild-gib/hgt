import GaloisForLFunctions.HTGeometry.FrullaniIntegral

/-!
# The weighted spectrum of a reflected Mellin pair

On a half-line, two exponential evaluation vectors with positive decay rates
have an explicit Gram matrix. Their normalized sum and difference give the
sharp upper and lower bounds of the reflected pairing. A common oscillatory
phase does not change either bound.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set Complex
open scoped InnerProductSpace

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity.WeightedReflectedPair

section HilbertPair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Hermitian contribution of two reflected evaluation vectors. -/
def pairForm (u v f : E) : ℝ :=
  2 * (inner ℂ u f * starRingEnd ℂ (inner ℂ v f)).re

theorem pairForm_real_smul (u v f : E) (c d : ℝ) :
    pairForm ((c : ℂ) • u) ((d : ℂ) • v) f = c * d * pairForm u v f := by
  simp only [pairForm, inner_smul_left, map_mul, Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  ring

private theorem complex_polarization (z w : ℂ) :
    4 * (z * starRingEnd ℂ w).re = ‖z + w‖ ^ 2 - ‖z - w‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The negative direction is the difference of the two unit evaluation vectors. -/
theorem unit_pairForm_lower {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (f : E) :
    ((inner ℂ u v).re - 1) * ‖f‖ ^ 2 ≤ pairForm u v f := by
  have hcs := pow_le_pow_left₀ (norm_nonneg (inner ℂ (u - v) f))
    (norm_inner_le_norm (u - v) f) 2
  rw [mul_pow, norm_sub_sq (𝕜 := ℂ), hu, hv, inner_sub_left] at hcs
  have hp := complex_polarization (inner ℂ u f) (inner ℂ v f)
  have hpos := sq_nonneg ‖inner ℂ u f + inner ℂ v f‖
  unfold pairForm
  norm_num only [one_pow] at hcs
  change ‖inner ℂ u f - inner ℂ v f‖ ^ 2 ≤
    (1 - 2 * (inner ℂ u v).re + 1) * ‖f‖ ^ 2 at hcs
  nlinarith only [hcs, hp, hpos]

/-- The positive direction is the sum of the two unit evaluation vectors. -/
theorem unit_pairForm_upper {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (f : E) :
    pairForm u v f ≤ ((inner ℂ u v).re + 1) * ‖f‖ ^ 2 := by
  have hcs := pow_le_pow_left₀ (norm_nonneg (inner ℂ (u + v) f))
    (norm_inner_le_norm (u + v) f) 2
  rw [mul_pow, norm_add_sq (𝕜 := ℂ), hu, hv, inner_add_left] at hcs
  have hp := complex_polarization (inner ℂ u f) (inner ℂ v f)
  have hpos := sq_nonneg ‖inner ℂ u f - inner ℂ v f‖
  unfold pairForm
  norm_num only [one_pow] at hcs
  change ‖inner ℂ u f + inner ℂ v f‖ ^ 2 ≤
    (1 + 2 * (inner ℂ u v).re + 1) * ‖f‖ ^ 2 at hcs
  nlinarith only [hcs, hp, hpos]

/-- A real mutual inner product makes the difference attain the lower bound. -/
theorem unit_pairForm_sub_eq {u v : E} {r : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℂ u v = (r : ℂ)) :
    pairForm u v (u - v) = (r - 1) * ‖u - v‖ ^ 2 := by
  have hvu : inner ℂ v u = (r : ℂ) := by
    rw [← inner_conj_symm v u, huv, Complex.conj_ofReal]
  have huu : inner ℂ u u = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have hvv : inner ℂ v v = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; norm_num
  rw [pairForm, inner_sub_right, inner_sub_right, huu, hvv, huv, hvu,
    norm_sub_sq (𝕜 := ℂ), hu, hv, huv]
  change 2 * ((1 - (r : ℂ)) * starRingEnd ℂ ((r : ℂ) - 1)).re =
    (r - 1) * (1 ^ 2 - 2 * r + 1 ^ 2)
  simp only [map_sub, map_one, Complex.conj_ofReal, Complex.sub_re, Complex.mul_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.one_im, sub_zero, mul_zero, one_pow]
  ring

/-- The sum attains the upper bound. -/
theorem unit_pairForm_add_eq {u v : E} {r : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℂ u v = (r : ℂ)) :
    pairForm u v (u + v) = (r + 1) * ‖u + v‖ ^ 2 := by
  have hvu : inner ℂ v u = (r : ℂ) := by
    rw [← inner_conj_symm v u, huv, Complex.conj_ofReal]
  have huu : inner ℂ u u = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have hvv : inner ℂ v v = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; norm_num
  rw [pairForm, inner_add_right, inner_add_right, huu, hvv, huv, hvu,
    norm_add_sq (𝕜 := ℂ), hu, hv, huv]
  change 2 * ((1 + (r : ℂ)) * starRingEnd ℂ ((r : ℂ) + 1)).re =
    (r + 1) * (1 ^ 2 + 2 * r + 1 ^ 2)
  simp only [map_add, map_one, Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.one_im, add_zero, mul_zero, sub_zero, one_pow]
  ring

end HilbertPair

/-- Square-integrable complex functions on the positive half-line. -/
abbrev HalfLineSpace := Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

/-- A decaying wave; the ordinate is a common unitary modulation. -/
def wave (a γ t : ℝ) : ℂ :=
  Complex.exp (-(((a : ℂ) + (γ : ℂ) * Complex.I) * (t : ℂ)))

theorem norm_wave (a γ t : ℝ) : ‖wave a γ t‖ = Real.exp (-a * t) := by
  rw [wave, Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul,
    add_zero]
  ring

theorem memLp_wave {a : ℝ} (ha : 0 < a) (γ : ℝ) :
    MemLp (wave a γ) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hc : Continuous (wave a γ) := by unfold wave; fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have he : (fun t : ℝ => ‖wave a γ t‖ ^ 2) = fun t => Real.exp (-(2 * a) * t) := by
    funext t
    rw [norm_wave, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact exp_neg_integrableOn_Ioi 0 (by linarith only [ha])

/-- The half-line evaluation vector with positive decay. -/
def vector (a : ℝ) (ha : 0 < a) (γ : ℝ) : HalfLineSpace :=
  (memLp_wave ha γ).toLp (wave a γ)

/-- A unit evaluation vector, normalized by its exact exponential mass. -/
def unitVector (a : ℝ) (ha : 0 < a) (γ : ℝ) : HalfLineSpace :=
  ((Real.sqrt (2 * a) : ℝ) : ℂ) • vector a ha γ

/-- The common oscillation cancels in the exponential Gram matrix. -/
theorem inner_vector {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (γ : ℝ) :
    inner ℂ (vector a ha γ) (vector b hb γ) = ((1 / (a + b) : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have hpoint : ∀ t : ℝ,
      inner ℂ (wave a γ t) (wave b γ t) =
        Complex.exp (-(((a + b : ℝ) : ℂ) * (t : ℂ))) := by
    intro t
    rw [RCLike.inner_apply, wave, wave, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_neg, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_add]
    ring
  calc
    _ = ∫ t in Ioi (0 : ℝ), Complex.exp (-(((a + b : ℝ) : ℂ) * (t : ℂ))) := by
      apply integral_congr_ae
      filter_upwards [(memLp_wave ha γ).coeFn_toLp, (memLp_wave hb γ).coeFn_toLp]
        with t hat hbt
      change inner ℂ ((memLp_wave ha γ).toLp (wave a γ) t)
        ((memLp_wave hb γ).toLp (wave b γ) t) = _
      rw [hat, hbt, hpoint]
    _ = 1 / ((a + b : ℝ) : ℂ) :=
      HTGeometry.integral_cexp_neg_mul (by simpa only [Complex.ofReal_re] using add_pos ha hb)
    _ = _ := by push_cast; rfl

/-- The exact overlap of the two normalized evaluation vectors. -/
theorem inner_unitVector {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (γ : ℝ) :
    inner ℂ (unitVector a ha γ) (unitVector b hb γ) =
      ((Real.sqrt (2 * a) * Real.sqrt (2 * b) / (a + b) : ℝ) : ℂ) := by
  rw [unitVector, unitVector, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, inner_vector ha hb]
  push_cast
  ring

theorem norm_unitVector {a : ℝ} (ha : 0 < a) (γ : ℝ) : ‖unitVector a ha γ‖ = 1 := by
  have h : ‖unitVector a ha γ‖ ^ 2 =
      Real.sqrt (2 * a) * Real.sqrt (2 * a) / (a + a) := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_unitVector]
    rfl
  have hs : Real.sqrt (2 * a) * Real.sqrt (2 * a) = 2 * a :=
    Real.mul_self_sqrt (by linarith only [ha])
  rw [hs, show a + a = 2 * a by ring, div_self (by positivity : 2 * a ≠ 0)] at h
  have hnorm := norm_nonneg (unitVector a ha γ)
  nlinarith only [h, hnorm]

/-- Product of the two normalization factors. -/
def scale (a b : ℝ) : ℝ := Real.sqrt (2 * a) * Real.sqrt (2 * b)

theorem scale_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < scale a b := by
  unfold scale
  positivity

theorem scale_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    scale a b ^ 2 = 4 * a * b := by
  rw [scale, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * a),
    Real.sq_sqrt (by positivity : 0 ≤ 2 * b)]
  ring

theorem scale_lt_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    scale a b < a + b := by
  have hs := scale_pos ha hb
  have hs2 := scale_sq ha hb
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hd : 0 < (a - b) ^ 2 := by positivity
  nlinarith only [hs, hs2, hd, ha, hb]

theorem pairForm_unitVector {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (γ : ℝ) (f : HalfLineSpace) :
    pairForm (unitVector a ha γ) (unitVector b hb γ) f =
      scale a b * pairForm (vector a ha γ) (vector b hb γ) f :=
  pairForm_real_smul _ _ _ _ _

/-- Sharp lower bound of the reflected pairing with positive decay rates. -/
theorem pairForm_lower {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (γ : ℝ) (f : HalfLineSpace) :
    (1 / (a + b) - 1 / scale a b) * ‖f‖ ^ 2 ≤
      pairForm (vector a ha γ) (vector b hb γ) f := by
  have hs := scale_pos ha hb
  have h := unit_pairForm_lower (norm_unitVector ha γ) (norm_unitVector hb γ) f
  rw [pairForm_unitVector, inner_unitVector, Complex.ofReal_re] at h
  change (scale a b / (a + b) - 1) * ‖f‖ ^ 2 ≤ _ at h
  refine le_of_mul_le_mul_left ?_ hs
  calc
    _ = (scale a b / (a + b) - 1) * ‖f‖ ^ 2 := by
      field_simp [ne_of_gt hs, ne_of_gt (add_pos ha hb)]
    _ ≤ _ := h

/-- Sharp upper bound of the reflected pairing with positive decay rates. -/
theorem pairForm_upper {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (γ : ℝ) (f : HalfLineSpace) :
    pairForm (vector a ha γ) (vector b hb γ) f ≤
      (1 / (a + b) + 1 / scale a b) * ‖f‖ ^ 2 := by
  have hs := scale_pos ha hb
  have h := unit_pairForm_upper (norm_unitVector ha γ) (norm_unitVector hb γ) f
  rw [pairForm_unitVector, inner_unitVector, Complex.ofReal_re] at h
  change _ ≤ (scale a b / (a + b) + 1) * ‖f‖ ^ 2 at h
  refine le_of_mul_le_mul_left ?_ hs
  calc
    _ ≤ (scale a b / (a + b) + 1) * ‖f‖ ^ 2 := h
    _ = _ := by
      field_simp [ne_of_gt hs, ne_of_gt (add_pos ha hb)]

/-- The normalized difference attains the lower bound. -/
theorem pairForm_sub_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (γ : ℝ) :
    pairForm (vector a ha γ) (vector b hb γ)
        (unitVector a ha γ - unitVector b hb γ) =
      (1 / (a + b) - 1 / scale a b) *
        ‖unitVector a ha γ - unitVector b hb γ‖ ^ 2 := by
  have hs := scale_pos ha hb
  have h := unit_pairForm_sub_eq (norm_unitVector ha γ) (norm_unitVector hb γ)
    (inner_unitVector ha hb γ)
  rw [pairForm_unitVector] at h
  change scale a b * _ = (scale a b / (a + b) - 1) * _ at h
  apply (mul_left_cancel₀ (ne_of_gt hs))
  calc
    _ = (scale a b / (a + b) - 1) *
        ‖unitVector a ha γ - unitVector b hb γ‖ ^ 2 := h
    _ = _ := by
      field_simp [ne_of_gt hs, ne_of_gt (add_pos ha hb)]

/-- The normalized sum attains the upper bound. -/
theorem pairForm_add_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (γ : ℝ) :
    pairForm (vector a ha γ) (vector b hb γ)
        (unitVector a ha γ + unitVector b hb γ) =
      (1 / (a + b) + 1 / scale a b) *
        ‖unitVector a ha γ + unitVector b hb γ‖ ^ 2 := by
  have hs := scale_pos ha hb
  have h := unit_pairForm_add_eq (norm_unitVector ha γ) (norm_unitVector hb γ)
    (inner_unitVector ha hb γ)
  rw [pairForm_unitVector] at h
  change scale a b * _ = (scale a b / (a + b) + 1) * _ at h
  apply (mul_left_cancel₀ (ne_of_gt hs))
  calc
    _ = (scale a b / (a + b) + 1) *
        ‖unitVector a ha γ + unitVector b hb γ‖ ^ 2 := h
    _ = _ := by
      field_simp [ne_of_gt hs, ne_of_gt (add_pos ha hb)]

/-- Unequal decay rates give a nonzero negative direction. -/
theorem pairForm_sub_neg {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (γ : ℝ) :
    pairForm (vector a ha γ) (vector b hb γ)
      (unitVector a ha γ - unitVector b hb γ) < 0 := by
  have hs := scale_pos ha hb
  have hsum := add_pos ha hb
  have hlt := scale_lt_add ha hb hab
  have hr : scale a b / (a + b) < 1 := (div_lt_one hsum).mpr hlt
  have hnorm : ‖unitVector a ha γ - unitVector b hb γ‖ ^ 2 =
      2 - 2 * (scale a b / (a + b)) := by
    rw [norm_sub_sq (𝕜 := ℂ), norm_unitVector, norm_unitVector, inner_unitVector]
    change 1 ^ 2 - 2 * (scale a b / (a + b)) + 1 ^ 2 = _
    ring
  have hn : 0 < ‖unitVector a ha γ - unitVector b hb γ‖ ^ 2 := by
    rw [hnorm]
    linarith only [hr]
  have hc : 1 / (a + b) - 1 / scale a b < 0 := by
    have hid : scale a b * (1 / (a + b) - 1 / scale a b) =
        scale a b / (a + b) - 1 := by
      field_simp [ne_of_gt hs, ne_of_gt hsum]
    nlinarith only [hs, hr, hid]
  rw [pairForm_sub_eq]
  exact mul_neg_of_neg_of_pos hc hn

/-- The positive direction is nonzero, including when the rates coincide. -/
theorem pairForm_add_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (γ : ℝ) :
    0 < pairForm (vector a ha γ) (vector b hb γ)
      (unitVector a ha γ + unitVector b hb γ) := by
  have hs := scale_pos ha hb
  have hsum := add_pos ha hb
  have hnorm : ‖unitVector a ha γ + unitVector b hb γ‖ ^ 2 =
      2 + 2 * (scale a b / (a + b)) := by
    rw [norm_add_sq (𝕜 := ℂ), norm_unitVector, norm_unitVector, inner_unitVector]
    change 1 ^ 2 + 2 * (scale a b / (a + b)) + 1 ^ 2 = _
    ring
  rw [pairForm_add_eq, hnorm]
  positivity

/-- At the critical line the two evaluation vectors coincide and the pair is nonnegative. -/
theorem pairForm_same_nonneg {a : ℝ} (ha : 0 < a) (γ : ℝ) (f : HalfLineSpace) :
    0 ≤ pairForm (vector a ha γ) (vector a ha γ) f := by
  have h := pairForm_lower ha ha γ f
  have hs : scale a a = 2 * a := Real.mul_self_sqrt (by positivity)
  rw [hs, show a + a = 2 * a by ring, sub_self, zero_mul] at h
  exact h

/-- Equality of the two decay rates is precisely positivity of the reflected form. -/
theorem pairForm_nonneg_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (γ : ℝ) :
    (∀ f : HalfLineSpace, 0 ≤ pairForm (vector a ha γ) (vector b hb γ) f) ↔ a = b := by
  constructor
  · intro h
    by_contra hab
    exact (not_lt_of_ge (h _)) (pairForm_sub_neg ha hb hab γ)
  · rintro rfl
    exact pairForm_same_nonneg ha γ

/-- No larger lower coefficient is possible for two distinct decay rates. -/
theorem pairForm_lower_optimal_of_ne {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (γ c : ℝ)
    (h : ∀ f : HalfLineSpace,
      c * ‖f‖ ^ 2 ≤ pairForm (vector a ha γ) (vector b hb γ) f) :
    c ≤ 1 / (a + b) - 1 / scale a b := by
  have hn : 0 < ‖unitVector a ha γ - unitVector b hb γ‖ ^ 2 := by
    have hneg := pairForm_sub_neg ha hb hab γ
    rw [pairForm_sub_eq] at hneg
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) (sq_nonneg ‖unitVector a ha γ - unitVector b hb γ‖)
    rw [hz, mul_zero] at hneg
    exact (lt_irrefl 0) hneg
  have hw := h (unitVector a ha γ - unitVector b hb γ)
  rw [pairForm_sub_eq] at hw
  exact le_of_mul_le_mul_left (by simpa only [mul_comm] using hw) hn

/-- A second exponential supplies a nonzero null vector when the two rates coincide. -/
def sameRateNullVector (a : ℝ) (ha : 0 < a) (γ : ℝ) : HalfLineSpace :=
  vector (2 * a) (by linarith only [ha]) γ - ((2 / 3 : ℝ) : ℂ) • vector a ha γ

theorem inner_sameRateNullVector {a : ℝ} (ha : 0 < a) (γ : ℝ) :
    inner ℂ (vector a ha γ) (sameRateNullVector a ha γ) = 0 := by
  simp only [sameRateNullVector, inner_sub_right, inner_smul_right, inner_vector]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt ha)]
  ring

theorem norm_sameRateNullVector_sq {a : ℝ} (ha : 0 < a) (γ : ℝ) :
    ‖sameRateNullVector a ha γ‖ ^ 2 = 1 / (36 * a) := by
  have h : inner ℂ (sameRateNullVector a ha γ) (sameRateNullVector a ha γ) =
      ((1 / (36 * a) : ℝ) : ℂ) := by
    simp only [sameRateNullVector, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal, inner_vector]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt ha)]
    ring
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), h]
  rfl

/-- The lower coefficient remains optimal when both evaluations coincide. -/
theorem pairForm_lower_optimal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (γ c : ℝ)
    (h : ∀ f : HalfLineSpace,
      c * ‖f‖ ^ 2 ≤ pairForm (vector a ha γ) (vector b hb γ) f) :
    c ≤ 1 / (a + b) - 1 / scale a b := by
  by_cases hab : a = b
  · subst b
    have hw := h (sameRateNullVector a ha γ)
    rw [pairForm, inner_sameRateNullVector, zero_mul, Complex.zero_re, mul_zero,
      norm_sameRateNullVector_sq] at hw
    have hc : c ≤ 0 := le_of_mul_le_mul_left
      (by simpa only [mul_comm, mul_zero, zero_mul] using hw)
      (by positivity : 0 < 1 / (36 * a))
    have hs : scale a a = 2 * a := Real.mul_self_sqrt (by positivity)
    simpa only [hs, show a + a = 2 * a by ring, sub_self] using hc
  · exact pairForm_lower_optimal_of_ne ha hb hab γ c h

/-- No smaller upper coefficient is possible. -/
theorem pairForm_upper_optimal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (γ c : ℝ)
    (h : ∀ f : HalfLineSpace,
      pairForm (vector a ha γ) (vector b hb γ) f ≤ c * ‖f‖ ^ 2) :
    1 / (a + b) + 1 / scale a b ≤ c := by
  have hn : 0 < ‖unitVector a ha γ + unitVector b hb γ‖ ^ 2 := by
    have hpos := pairForm_add_pos ha hb γ
    rw [pairForm_add_eq] at hpos
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) (sq_nonneg ‖unitVector a ha γ + unitVector b hb γ‖)
    rw [hz, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  have hw := h (unitVector a ha γ + unitVector b hb γ)
  rw [pairForm_add_eq] at hw
  exact le_of_mul_le_mul_left (by simpa only [mul_comm] using hw) hn

theorem leftRate_pos {p δ : ℝ} (hp : 2 * |δ| < p) : 0 < p / 2 + δ := by
  linarith only [hp, neg_le_abs δ]

theorem rightRate_pos {p δ : ℝ} (hp : 2 * |δ| < p) : 0 < p / 2 - δ := by
  linarith only [hp, le_abs_self δ]

/-- The scale of a reflected pair in weight coordinates. -/
theorem scale_weighted {p δ : ℝ} (hp : 2 * |δ| < p) :
    scale (p / 2 + δ) (p / 2 - δ) = Real.sqrt (p ^ 2 - 4 * δ ^ 2) := by
  have hs := scale_pos (leftRate_pos hp) (rightRate_pos hp)
  have hs2 := scale_sq (leftRate_pos hp) (rightRate_pos hp)
  have hr : 0 ≤ p ^ 2 - 4 * δ ^ 2 := by
    nlinarith only [hs2, sq_nonneg (scale (p / 2 + δ) (p / 2 - δ))]
  have hr2 := Real.sq_sqrt hr
  have hr0 := Real.sqrt_nonneg (p ^ 2 - 4 * δ ^ 2)
  nlinarith only [hs, hs2, hr2, hr0]

/-- Conjugating the negative-half-line weight gives these two evaluation vectors. -/
def weightedPairForm (p δ : ℝ) (hp : 2 * |δ| < p) (γ : ℝ) (f : HalfLineSpace) : ℝ :=
  pairForm (vector (p / 2 + δ) (leftRate_pos hp) γ)
    (vector (p / 2 - δ) (rightRate_pos hp) γ) f

/-- Exact ordinate-independent bounds in weight and horizontal-displacement coordinates. -/
theorem weightedPairForm_bounds {p δ : ℝ} (hp : 2 * |δ| < p)
    (γ : ℝ) (f : HalfLineSpace) :
    (1 / p - 1 / Real.sqrt (p ^ 2 - 4 * δ ^ 2)) * ‖f‖ ^ 2 ≤
        weightedPairForm p δ hp γ f ∧
      weightedPairForm p δ hp γ f ≤
        (1 / p + 1 / Real.sqrt (p ^ 2 - 4 * δ ^ 2)) * ‖f‖ ^ 2 := by
  have hsum : p / 2 + δ + (p / 2 - δ) = p := by ring
  have hl := pairForm_lower (leftRate_pos hp) (rightRate_pos hp) γ f
  have hu := pairForm_upper (leftRate_pos hp) (rightRate_pos hp) γ f
  rw [hsum, scale_weighted hp] at hl hu
  exact ⟨hl, hu⟩

/-- A reflected pair is positive on every test precisely at zero horizontal displacement. -/
theorem weightedPairForm_nonneg_iff {p δ : ℝ} (hp : 2 * |δ| < p) (γ : ℝ) :
    (∀ f : HalfLineSpace, 0 ≤ weightedPairForm p δ hp γ f) ↔ δ = 0 := by
  unfold weightedPairForm
  rw [pairForm_nonneg_iff]
  constructor <;> intro h <;> linarith only [h]

#print axioms weightedPairForm_bounds
#print axioms weightedPairForm_nonneg_iff
#print axioms pairForm_lower_optimal
#print axioms pairForm_upper_optimal

end GaloisForLFunctions.ArithmeticCorrespondencePositivity.WeightedReflectedPair
