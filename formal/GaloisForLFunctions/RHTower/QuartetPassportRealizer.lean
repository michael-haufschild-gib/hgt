import GaloisForLFunctions.RHTower.CoshPolynomialQuasiPeriod
import GaloisForLFunctions.RHTower.CoshPolynomialExactOrderOne

/-!
# The realized entire function of the quartet-passport construction

`F = A · B`, the displaced cosh quartet envelope times the interpolating polynomial, carries all the
*global* guards of the arbitrary-finite-quartet-passport realization.  This module collects them,
each one reduced to the corresponding statement about the two factors:

* `quartetRealizer_neg`, `quartetRealizer_conj` — evenness and Schwarz reality;
* `quartetRealizer_pos_real_on_imaginaryAxis`, `quartetRealizer_ne_zero_on_imaginaryAxis` — the
  zero-free axis, from strict positivity of *both* factors there
  (`coshQuartetEnvelope_mul_I_pos_real` and the positive repair);
* `quartetRealizer_periodic_iff` — aperiodicity;
* `quartetRealizer_quasiPeriodic_eq_zero` — the strictly stronger statement needed for full-germ
  separation: no nonzero displacement is absorbed even up to a multiplicative constant;
* `quartetRealizer_exact_order_one_bounds` — the two-sided exponential envelope certifying exact
  entire order one.

`quartetRealizerStrip` is the affine transfer `X(s) = F(-i(s - 1/2))` back to the critical-strip
coordinate, where evenness becomes the functional equation `X(1-s) = X(s)`
(`quartetRealizerStrip_one_sub`), Schwarz reality is preserved
(`quartetRealizerStrip_conj`), and the zero-free imaginary axis becomes a zero-free *real* axis
(`quartetRealizerStrip_ne_zero_on_realAxis`).
-/

noncomputable section

open Complex Polynomial

namespace RHTower



/-- The realized entire function of the quartet-passport construction, in centered coordinates. -/
def quartetRealizer (a : ℝ) (B : Polynomial ℂ) (z : ℂ) : ℂ :=
  coshQuartetEnvelope a z * B.eval z

theorem quartetRealizer_analyticAt (a : ℝ) (B : Polynomial ℂ) (z : ℂ) :
    AnalyticAt ℂ (quartetRealizer a B) z :=
  (coshQuartetEnvelope_analyticAt a z).mul ((Polynomial.differentiable B).analyticAt z)

theorem quartetRealizer_differentiable (a : ℝ) (B : Polynomial ℂ) :
    Differentiable ℂ (quartetRealizer a B) :=
  fun z => (quartetRealizer_analyticAt a B z).differentiableAt

/-- **Evenness.**  With a real-even polynomial factor the realizer is even. -/
theorem quartetRealizer_neg {a : ℝ} {B : Polynomial ℂ}
    (hB : ∀ z : ℂ, B.eval (-z) = B.eval z) (z : ℂ) :
    quartetRealizer a B (-z) = quartetRealizer a B z := by
  rw [quartetRealizer, quartetRealizer, coshQuartetEnvelope_neg, hB]

/-- **Schwarz reality.** -/
theorem quartetRealizer_conj {a : ℝ} {B : Polynomial ℂ}
    (hB : ∀ z : ℂ, B.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (B.eval z)) (z : ℂ) :
    quartetRealizer a B ((starRingEnd ℂ) z) = (starRingEnd ℂ) (quartetRealizer a B z) := by
  rw [quartetRealizer, quartetRealizer, coshQuartetEnvelope_conj, hB, map_mul]

/-- **Strict positivity on the imaginary axis.**  Both factors are strictly positive real there. -/
theorem quartetRealizer_pos_real_on_imaginaryAxis {a : ℝ} (ha : a ≠ 0) {B : Polynomial ℂ}
    (hB : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ B.eval ((y : ℂ) * I) = (r : ℂ)) (y : ℝ) :
    ∃ r : ℝ, 0 < r ∧ quartetRealizer a B ((y : ℂ) * I) = (r : ℂ) := by
  obtain ⟨rA, hrA, hAeq⟩ := coshQuartetEnvelope_mul_I_pos_real (a := a) (y := y) ha
  obtain ⟨rB, hrB, hBeq⟩ := hB y
  refine ⟨rA * rB, mul_pos hrA hrB, ?_⟩
  rw [quartetRealizer, hAeq, hBeq]
  push_cast
  ring

/-- **Zero-free imaginary axis.** -/
theorem quartetRealizer_ne_zero_on_imaginaryAxis {a : ℝ} (ha : a ≠ 0) {B : Polynomial ℂ}
    (hB : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ B.eval ((y : ℂ) * I) = (r : ℂ)) (y : ℝ) :
    quartetRealizer a B ((y : ℂ) * I) ≠ 0 := by
  obtain ⟨r, hr, heq⟩ := quartetRealizer_pos_real_on_imaginaryAxis ha hB y
  rw [heq]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt hr)

/-- **Aperiodicity.**  The period group of the realizer is trivial. -/
theorem quartetRealizer_periodic_iff {a : ℝ} (ha : a ≠ 0) {B : Polynomial ℂ}
    (hdeg : 0 < B.degree) (h : ℂ) :
    Function.Periodic (quartetRealizer a B) h ↔ h = 0 :=
  coshQuartetEnvelope_mul_polynomial_periodic_iff a ha B hdeg h

/-- **No nonzero quasi-period.**  This is the full-germ separation step: a nonzero displacement
cannot be absorbed even up to a nonzero multiplicative constant. -/
theorem quartetRealizer_quasiPeriodic_eq_zero {a : ℝ} (ha : a ≠ 0) {B : Polynomial ℂ}
    (hdeg : 0 < B.degree) {h C : ℂ} (hC : C ≠ 0)
    (hq : ∀ z : ℂ, quartetRealizer a B (z + h) = C * quartetRealizer a B z) :
    h = 0 :=
  coshQuartetEnvelope_mul_polynomial_quasiPeriodic_eq_zero a ha B hdeg hC hq

/-- **Exact entire order one.** -/
theorem quartetRealizer_exact_order_one_bounds (a : ℝ) {B : Polynomial ℂ} (hB : B ≠ 0) :
    ∃ Kupper Klower R : ℝ,
      0 < Kupper ∧ 0 < Klower ∧
      (∀ z : ℂ, ‖quartetRealizer a B z‖ ≤
        Kupper * (1 + ‖z‖) ^ B.natDegree * Real.exp (2 * ‖z‖)) ∧
      ∀ x : ℝ, R ≤ x → Klower * Real.exp (2 * x) ≤ ‖quartetRealizer a B (x : ℂ)‖ :=
  coshQuartetEnvelope_mul_polynomial_exact_order_one_bounds a hB

/-! ## Transfer to the critical-strip coordinate -/

/-- The realized function in the `s` coordinate: `X(s) = F(-i(s - 1/2))`. -/
def quartetRealizerStrip (a : ℝ) (B : Polynomial ℂ) (s : ℂ) : ℂ :=
  quartetRealizer a B (-I * (s - ((1 / 2 : ℝ) : ℂ)))

/-- **The functional equation `X(1-s) = X(s)`.** -/
theorem quartetRealizerStrip_one_sub {a : ℝ} {B : Polynomial ℂ}
    (hB : ∀ z : ℂ, B.eval (-z) = B.eval z) (s : ℂ) :
    quartetRealizerStrip a B (1 - s) = quartetRealizerStrip a B s := by
  rw [quartetRealizerStrip, quartetRealizerStrip]
  have hcoord : -I * ((1 - s) - ((1 / 2 : ℝ) : ℂ))
      = -(-I * (s - ((1 / 2 : ℝ) : ℂ))) := by
    push_cast
    ring
  rw [hcoord, quartetRealizer_neg hB]

/-- **Schwarz symmetry `X(conj s) = conj (X s)`.** -/
theorem quartetRealizerStrip_conj {a : ℝ} {B : Polynomial ℂ}
    (hBeven : ∀ z : ℂ, B.eval (-z) = B.eval z)
    (hBreal : ∀ z : ℂ, B.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (B.eval z)) (s : ℂ) :
    quartetRealizerStrip a B ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (quartetRealizerStrip a B s) := by
  rw [quartetRealizerStrip, quartetRealizerStrip]
  have hcoord : -I * ((starRingEnd ℂ) s - ((1 / 2 : ℝ) : ℂ))
      = -((starRingEnd ℂ) (-I * (s - ((1 / 2 : ℝ) : ℂ)))) := by
    rw [map_mul, map_sub, map_neg, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hcoord, quartetRealizer_neg hBeven, quartetRealizer_conj hBreal]

/-- **The real axis of the strip coordinate is zero-free.** -/
theorem quartetRealizerStrip_ne_zero_on_realAxis {a : ℝ} (ha : a ≠ 0) {B : Polynomial ℂ}
    (hB : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ B.eval ((y : ℂ) * I) = (r : ℂ)) (t : ℝ) :
    quartetRealizerStrip a B (t : ℂ) ≠ 0 := by
  have hcoord : -I * ((t : ℂ) - ((1 / 2 : ℝ) : ℂ)) = ((1 / 2 - t : ℝ) : ℂ) * I := by
    push_cast
    ring_nf
  rw [quartetRealizerStrip, hcoord]
  exact quartetRealizer_ne_zero_on_imaginaryAxis ha hB (1 / 2 - t)


end RHTower

end
