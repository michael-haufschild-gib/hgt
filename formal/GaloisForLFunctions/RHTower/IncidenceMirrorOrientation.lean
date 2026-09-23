/-
The endpoint-orientation effect of the reciprocal incidence mirror.

For an FE-paired pencil, the incidence mirror has the form `z ↦ (ε'/ε)/z`.  When the
mirror constant is positive real, this map reverses the sign of the imaginary part:
it sends upper-half-plane incidence values to lower-half-plane values and conversely.  Thus
the positive-real mirror relation supplies an opposite-edge orientation rule, not by itself
the same-edge endpoint agreement consumed by `EdgeEventParity`.
-/
import GaloisForLFunctions.RHTower.IncidenceCarrier

namespace RHTower

open Complex

/-- The imaginary part of a positive-real reciprocal mirror, in closed form. -/
theorem im_real_div_eq_neg_normSq (lam : ℝ) (z : ℂ) :
    (((lam : ℂ) / z).im) = -lam * z.im / Complex.normSq z := by
  rw [Complex.div_im]
  simp only [Complex.ofReal_im, zero_mul, Complex.ofReal_re, zero_div]
  ring

/-- A positive real reciprocal sends the lower half plane to the upper half plane. -/
theorem im_real_div_pos_iff_neg {lam : ℝ} {z : ℂ} (hlam : 0 < lam) (hz : z ≠ 0) :
    0 < (((lam : ℂ) / z).im) ↔ z.im < 0 := by
  rw [im_real_div_eq_neg_normSq]
  constructor
  · intro h
    by_contra hnon
    have hznon : 0 ≤ z.im := le_of_not_gt hnon
    have hle : -lam * z.im / Complex.normSq z ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam.le) hznon)
        (Complex.normSq_nonneg z)
    exact not_lt_of_ge hle h
  · intro him
    exact div_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos hlam) him)
      (Complex.normSq_pos.mpr hz)

/-- A positive real reciprocal sends the upper half plane to the lower half plane. -/
theorem im_real_div_neg_iff_pos {lam : ℝ} {z : ℂ} (hlam : 0 < lam) (hz : z ≠ 0) :
    (((lam : ℂ) / z).im < 0) ↔ 0 < z.im := by
  rw [im_real_div_eq_neg_normSq]
  constructor
  · intro h
    by_contra hnon
    have hznon : z.im ≤ 0 := le_of_not_gt hnon
    have hge : 0 ≤ -lam * z.im / Complex.normSq z := by
      exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hlam.le) hznon)
        (Complex.normSq_nonneg z)
    exact not_lt_of_ge hge h
  · intro him
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hlam) him)
      (Complex.normSq_pos.mpr hz)

/-- A nonreal point and its positive-real reciprocal have opposite imaginary orientations. -/
theorem im_real_div_mul_im_neg {lam : ℝ} {z : ℂ} (hlam : 0 < lam) (hz : z ≠ 0)
    (him : z.im ≠ 0) :
    (((lam : ℂ) / z).im) * z.im < 0 := by
  rw [im_real_div_eq_neg_normSq]
  have hden : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hsq : 0 < z.im ^ (2 : ℕ) := sq_pos_of_ne_zero him
  have hnum : -(lam * z.im ^ (2 : ℕ)) < 0 := by
    have hprod : 0 < lam * z.im ^ (2 : ℕ) := mul_pos hlam hsq
    linarith
  have heq : (-lam * z.im / Complex.normSq z) * z.im =
      -(lam * z.im ^ (2 : ℕ)) / Complex.normSq z := by
    field_simp [hden.ne']
  rw [heq]
  exact div_neg_of_neg_of_pos hnum hden

/-- Under a positive-real FE incidence mirror, positive mirror orientation is negative source
orientation. -/
theorem incidence_mirror_im_pos_iff_neg_of_real_pos {Λ₁ Λ₂ : ℂ → ℂ} {ε ε' : ℂ}
    (hFE₁ : ∀ s, Λ₁ (1 - s) = ε * Λ₂ s) (hFE₂ : ∀ s, Λ₂ (1 - s) = ε' * Λ₁ s)
    {s : ℂ} (hε : ε ≠ 0) (hΛ₂ : Λ₂ s ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (hratio : ε' / ε = (lam : ℂ)) (hι : incidence Λ₁ Λ₂ s ≠ 0) :
    0 < (incidence Λ₁ Λ₂ (1 - s)).im ↔ (incidence Λ₁ Λ₂ s).im < 0 := by
  rw [incidence_mirror hFE₁ hFE₂ hε hΛ₂, hratio]
  exact im_real_div_pos_iff_neg hlam hι

/-- Under a positive-real FE incidence mirror, negative mirror orientation is positive source
orientation. -/
theorem incidence_mirror_im_neg_iff_pos_of_real_pos {Λ₁ Λ₂ : ℂ → ℂ} {ε ε' : ℂ}
    (hFE₁ : ∀ s, Λ₁ (1 - s) = ε * Λ₂ s) (hFE₂ : ∀ s, Λ₂ (1 - s) = ε' * Λ₁ s)
    {s : ℂ} (hε : ε ≠ 0) (hΛ₂ : Λ₂ s ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (hratio : ε' / ε = (lam : ℂ)) (hι : incidence Λ₁ Λ₂ s ≠ 0) :
    (incidence Λ₁ Λ₂ (1 - s)).im < 0 ↔ 0 < (incidence Λ₁ Λ₂ s).im := by
  rw [incidence_mirror hFE₁ hFE₂ hε hΛ₂, hratio]
  exact im_real_div_neg_iff_pos hlam hι

/-- The positive-real FE incidence mirror reverses the nonzero imaginary orientation. -/
theorem incidence_mirror_im_product_neg_of_real_pos {Λ₁ Λ₂ : ℂ → ℂ} {ε ε' : ℂ}
    (hFE₁ : ∀ s, Λ₁ (1 - s) = ε * Λ₂ s) (hFE₂ : ∀ s, Λ₂ (1 - s) = ε' * Λ₁ s)
    {s : ℂ} (hε : ε ≠ 0) (hΛ₂ : Λ₂ s ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (hratio : ε' / ε = (lam : ℂ)) (hι : incidence Λ₁ Λ₂ s ≠ 0)
    (him : (incidence Λ₁ Λ₂ s).im ≠ 0) :
    (incidence Λ₁ Λ₂ (1 - s)).im * (incidence Λ₁ Λ₂ s).im < 0 := by
  rw [incidence_mirror hFE₁ hFE₂ hε hΛ₂, hratio]
  exact im_real_div_mul_im_neg hlam hι him

end RHTower
