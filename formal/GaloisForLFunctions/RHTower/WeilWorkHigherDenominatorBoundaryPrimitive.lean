import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorFourierBoundary
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# A continuous primitive of the actual Fourier boundary

The original cubic datum supplies square-weighted coefficient summability.
Its Fourier boundary is the distributional second derivative of a bounded
continuous function, plus the actual constant term. Subtracting the primitive's
value at zero prepares an absolutely convergent Mellin overlap; it does not
assert regularity of the boundary distribution itself.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.WeilHigherDenominator


/-- The continuous second primitive of the nonconstant Fourier boundary. -/
def fourierBoundaryPrimitive (q : ℕ → ℂ) (x : ℝ) : ℂ :=
  (∑' n : ℕ, q (n + 1) / ((n + 1 : ℕ) : ℂ) ^ 2 *
    (Real.cos (2 * Real.pi * (n + 1) * x) : ℂ)) / (Real.pi : ℂ) ^ 2

private lemma primitive_term_norm_le (q : ℕ → ℂ) (n : ℕ) (x : ℝ) :
    ‖q (n + 1) / ((n + 1 : ℕ) : ℂ) ^ 2 *
      (Real.cos (2 * Real.pi * (n + 1) * x) : ℂ)‖ ≤
        ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

private lemma summable_primitive_term {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) (x : ℝ) :
    Summable fun n : ℕ => q (n + 1) / ((n + 1 : ℕ) : ℂ) ^ 2 *
      (Real.cos (2 * Real.pi * (n + 1) * x) : ℂ) :=
  hq.of_norm_bounded (fun n => primitive_term_norm_le q n x)

theorem continuous_fourierBoundaryPrimitive {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) :
    Continuous (fourierBoundaryPrimitive q) := by
  exact (continuous_tsum (fun n => by fun_prop) hq
    (fun n x => primitive_term_norm_le q n x)).div_const _

theorem norm_fourierBoundaryPrimitive_le {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) (x : ℝ) :
    ‖fourierBoundaryPrimitive q x‖ ≤
      (∑' n : ℕ, ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) / Real.pi ^ 2 := by
  rw [fourierBoundaryPrimitive, norm_div, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact (norm_tsum_le_tsum_norm ((hq.of_norm_bounded
    (fun n => primitive_term_norm_le q n x)).norm)).trans
      (Summable.tsum_le_tsum (fun n => primitive_term_norm_le q n x)
        ((summable_primitive_term hq x).norm) hq)

theorem fourierBoundaryPrimitive_sub_zero {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) (x : ℝ) :
    fourierBoundaryPrimitive q x - fourierBoundaryPrimitive q 0 =
      (∑' n : ℕ, q (n + 1) / ((n + 1 : ℕ) : ℂ) ^ 2 *
        ((Real.cos (2 * Real.pi * (n + 1) * x) : ℂ) - 1)) / (Real.pi : ℂ) ^ 2 := by
  rw [fourierBoundaryPrimitive, fourierBoundaryPrimitive, ← sub_div,
    ← (summable_primitive_term hq x).tsum_sub (summable_primitive_term hq 0)]
  congr 1
  apply tsum_congr
  intro n
  simp only [mul_zero, Real.cos_zero, Complex.ofReal_one, mul_one]
  ring

theorem cosineTestCoefficient_deriv_two {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ) (x : ℝ) :
    cosineTestCoefficient (deriv (deriv φ)) x =
      -(((2 * Real.pi * x : ℝ) : ℂ) ^ 2) * cosineTestCoefficient φ x := by
  simp only [cosineTestCoefficient, testTransformTwoPi]
  rw [← testTransform_ibp_two hφ hs, ← testTransform_ibp_two hφ hs]
  simp only [mul_pow, Complex.I_sq]
  push_cast
  ring

/-- Pairing the continuous primitive commutes with its full Fourier series. -/
theorem integral_test_fourierBoundaryPrimitive {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    {φ : ℝ → ℂ} (hc : Continuous φ) (hs : HasCompactSupport φ) :
    (∫ x : ℝ, φ x * fourierBoundaryPrimitive q x) =
      (∑' n : ℕ, q (n + 1) / ((n + 1 : ℕ) : ℂ) ^ 2 *
        cosineTestCoefficient φ (n + 1)) / (Real.pi : ℂ) ^ 2 := by
  let f (n : ℕ) (x : ℝ) := φ x * (q (n + 1) / ((n + 1 : ℕ) : ℂ) ^ 2 *
    (Real.cos (2 * Real.pi * (n + 1) * x) : ℂ))
  have hi : ∀ n, Integrable (f n) := fun n =>
    (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hs.mul_right
  have hiφ := hc.integrable_of_hasCompactSupport hs (μ := volume)
  have hsum : Summable fun n => ∫ x : ℝ, ‖f n x‖ := by
    apply (hq.mul_left (∫ x : ℝ, ‖φ x‖)).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    calc
      (∫ x : ℝ, ‖f n x‖) ≤ ∫ x : ℝ,
          ‖φ x‖ * (‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) := by
        apply integral_mono (hi n).norm (hiφ.norm.mul_const _)
        intro x
        exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left
          (primitive_term_norm_le q n x) (norm_nonneg _))
      _ = _ := integral_mul_const _ _
  calc
    (∫ x : ℝ, φ x * fourierBoundaryPrimitive q x) =
        (∫ x : ℝ, ∑' n, f n x) / (Real.pi : ℂ) ^ 2 := by
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [fourierBoundaryPrimitive, f, tsum_mul_left, mul_div_assoc]
    _ = (∑' n, ∫ x : ℝ, f n x) / (Real.pi : ℂ) ^ 2 := by
      rw [integral_tsum_of_summable_integral_norm hi hsum]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro n
      rw [cosineTestCoefficient_eq_integral hc hs, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [f]
      push_cast
      ring

/-- The actual Fourier boundary is the distributional second derivative plus its constant. -/
theorem fourierBoundaryPairing_eq_primitive {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    (A : ℂ) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    fourierBoundaryPairing q A φ = A * (∫ x : ℝ, φ x) +
      ∫ x : ℝ, deriv (deriv φ) x * fourierBoundaryPrimitive q x := by
  have hd := (contDiff_infty_iff_deriv.mp hφ).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  rw [integral_test_fourierBoundaryPrimitive hq hdd.continuous hs.deriv.deriv]
  have ht : ∀ n : ℕ,
      q (n + 1) / ((n + 1 : ℕ) : ℂ) ^ 2 *
        cosineTestCoefficient (deriv (deriv φ)) (n + 1) =
      (-4 * (Real.pi : ℂ) ^ 2) * (q (n + 1) * cosineTestCoefficient φ (n + 1)) := by
    intro n
    rw [cosineTestCoefficient_deriv_two hφ hs]
    have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    push_cast at hn ⊢
    field_simp
    ring
  simp_rw [ht]
  rw [tsum_mul_left]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold fourierBoundaryPairing
  field_simp
  ring

/-- All primitive bounds and the distributional identity are paid by the original cubic datum. -/
theorem degreeTwoQuotient_boundaryPrimitive {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) :
    Continuous (fourierBoundaryPrimitive (degreeTwoQuotientCoeff g)) ∧
      ∀ (A : ℂ) (φ : ℝ → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        fourierBoundaryPairing (degreeTwoQuotientCoeff g) A φ =
          A * (∫ x : ℝ, φ x) + ∫ x : ℝ,
            deriv (deriv φ) x * fourierBoundaryPrimitive (degreeTwoQuotientCoeff g) x := by
  have hq := degreeTwoQuotientCoeff_summable_shift_square hD
  exact ⟨continuous_fourierBoundaryPrimitive hq,
    fun A _ hφ hs => fourierBoundaryPairing_eq_primitive hq A hφ hs⟩

end RHTower.WeilHigherDenominator
