import GaloisForLFunctions.RHTower.CompleteHankelSignCone
import GaloisForLFunctions.RHTower.ExpDecayFourierAnalytic
import GaloisForLFunctions.HTGeometry.LocalExponentialTestClosure

/-!
# Completeness of unwindowed Hankel moments under exponential decay

A continuous exponentially decaying signed density is pointwise nonnegative exactly when every
finite Hankel section of its raw moments is positive semidefinite. A positive Laplace reference
measure makes the density a bounded multiplier. One local exponential window gives polynomial
density; splitting a complex polynomial into real and imaginary parts transfers the real Hankel
condition to the existing scalar sign theorem. The tested moments carry no Gaussian window.
-/

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Polynomial Set
open scoped ENNReal
namespace RHTower
noncomputable section

/-- Absolute exponential decay makes every raw moment integrable. -/
theorem integrable_rawMoment_of_expDecay {J : ℝ → ℝ} (hJ : Continuous J)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hbound : ∀ x, |J x| ≤ C * Real.exp (-(ε * |x|))) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * J x) := by
  have h := integrable_expDecay_mul_pow
    (Complex.continuous_ofReal.comp hJ).aestronglyMeasurable hC hε
    (fun x => by simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using hbound x) n
  simpa only [Function.comp_apply, RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re, ← Complex.ofReal_pow,
    Complex.ofReal_im, mul_zero, sub_zero, mul_comm] using h.re

/-- Raw polynomial integration agrees with the moment functional whenever every moment is
integrable. No window is inserted in the functional. -/
theorem momentFunctional_rawMoment_eq_integral {J : ℝ → ℝ}
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n * J x)) (p : Polynomial ℝ) :
    HTGeometry.momentFunctional (weightedMoment volume J) p =
      ∫ x, p.eval x * J x := by
  rw [HTGeometry.momentFunctional_eq_support_sum]
  have heval : (fun x : ℝ => p.eval x * J x) =
      fun x => ∑ k ∈ p.support, p.coeff k * (x ^ k * J x) := by
    funext x
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [heval, integral_finsetSum p.support (fun k _ => (hint k).const_mul _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul]
  rfl

/-- Integrability of arbitrary polynomial multiples from integrability of all raw moments. -/
theorem integrable_polynomial_mul_of_rawMoments {J : ℝ → ℝ}
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n * J x)) (p : Polynomial ℝ) :
    Integrable (fun x => p.eval x * J x) := by
  have h := integrable_finsetSum p.support (fun k _ => (hint k).const_mul (p.coeff k))
  convert h using 1 <;> try rfl
  funext x
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Complex polynomial modulus squares split into two real polynomial squares. -/
theorem exists_real_polynomials_norm_eval_sq (p : Polynomial ℂ) :
    ∃ r s : Polynomial ℝ, ∀ x : ℝ,
      ‖p.eval (x : ℂ)‖ ^ 2 = (r.eval x) ^ 2 + (s.eval x) ^ 2 := by
  classical
  let r : Polynomial ℝ := ∑ k ∈ p.support, C (p.coeff k).re * X ^ k
  let s : Polynomial ℝ := ∑ k ∈ p.support, C (p.coeff k).im * X ^ k
  refine ⟨r, s, fun x => ?_⟩
  have hr : r.eval x = (p.eval (x : ℂ)).re := by
    simp only [r, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    simp only [
      Complex.re_sum, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  have hs : s.eval x = (p.eval (x : ℂ)).im := by
    simp only [s, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    simp only [
      Complex.im_sum, ← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add]
  rw [hr, hs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- The unnormalised positive Laplace reference measure. -/
def laplaceReferenceMeasure (c : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-(c * |x|))))

instance laplaceReferenceMeasure_isOpenPosMeasure (c : ℝ) :
    (laplaceReferenceMeasure c).IsOpenPosMeasure where
  open_pos U hU hne := by
    intro hzero
    apply hU.measure_ne_zero volume hne
    unfold laplaceReferenceMeasure at hzero
    rw [withDensity_apply_eq_zero (by fun_prop)] at hzero
    have hset : {x : ℝ | ENNReal.ofReal (Real.exp (-(c * |x|))) ≠ 0} = univ := by
      ext x
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
    simpa only [hset, univ_inter] using hzero

/-- **Unwindowed complete moment sign law.** For a continuous exponentially decaying real
density, positivity of all raw Hankel sections is exactly pointwise nonnegativity. -/
theorem completeHankelCone_rawMoment_iff_of_expDecay {J : ℝ → ℝ} (hJ : Continuous J)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hbound : ∀ x, |J x| ≤ C * Real.exp (-(ε * |x|))) :
    CompleteHankelCone (weightedMoment volume J) ↔ ∀ x, 0 ≤ J x := by
  have hint := integrable_rawMoment_of_expDecay hJ hC hε hbound
  rw [completeHankelCone_iff_momentFunctional_square_nonnegative]
  have hsquare (p : Polynomial ℝ) : (fun x : ℝ => (p ^ 2).eval x * J x) =
      (fun x => (p.eval x) ^ 2 * J x) :=
    funext fun x => congrArg (fun v : ℝ => v * J x) (Polynomial.eval_pow (p := p) (x := x) 2)
  have hform (p : Polynomial ℝ) :
      HTGeometry.momentFunctional (weightedMoment volume J) (p ^ 2) =
        ∫ x, (p.eval x) ^ 2 * J x := by
    rw [momentFunctional_rawMoment_eq_integral hint (p ^ 2), hsquare]
  constructor
  · intro hpos
    let μ := laplaceReferenceMeasure (ε / 2)
    let g : ℝ → ℝ := fun x => Real.exp ((ε / 2) * |x|) * J x
    have hμ : IsFiniteMeasure μ :=
      isFiniteMeasure_withDensity_ofReal
        (integrable_exp_neg_mul_abs (half_pos hε)).hasFiniteIntegral
    letI := hμ
    have hgc : Continuous g := by fun_prop
    have hcancel (x : ℝ) : Real.exp (-(ε / 2 * |x|)) * g x = J x := by
      dsimp only [g]
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    have hbdd : ∀ x, |g x| ≤ C := by
      intro x
      dsimp only [g]
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (ε / 2 * |x|) * |J x| ≤
          Real.exp (ε / 2 * |x|) * (C * Real.exp (-(ε * |x|))) :=
            mul_le_mul_of_nonneg_left (hbound x) (Real.exp_pos _).le
        _ = C * Real.exp (-(ε / 2 * |x|)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
        _ ≤ C := by
          apply mul_le_of_le_one_right hC
          exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (half_pos hε).le (abs_nonneg x)))
    have hexp : Integrable (fun x : ℝ => Real.exp ((ε / 4) * |x|)) μ := by
      dsimp only [μ, laplaceReferenceMeasure]
      rw [integrable_withDensity_iff_integrable_smul₀' (by fun_prop)
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp_rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, ← Real.exp_add]
      convert integrable_exp_neg_mul_abs (by linarith : 0 < ε / 4) using 1 <;> try rfl
      funext x
      congr 1
      ring
    have hpoly : ∀ p : Polynomial ℂ,
        0 ≤ ∫ x : ℝ, ‖p.eval (x : ℂ)‖ ^ 2 * g x ∂μ := by
      intro p
      dsimp only [μ, laplaceReferenceMeasure]
      rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp_rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul,
        mul_left_comm _ (‖_‖ ^ 2), hcancel]
      obtain ⟨r, s, hrs⟩ := exists_real_polynomials_norm_eval_sq p
      simp_rw [hrs, add_mul]
      rw [integral_add
        (by rw [← hsquare r]; exact integrable_polynomial_mul_of_rawMoments hint (r ^ 2))
        (by rw [← hsquare s]; exact integrable_polynomial_mul_of_rawMoments hint (s ^ 2))]
      rw [← hform, ← hform]
      exact add_nonneg (hpos r) (hpos s)
    have hnonneg : 0 ≤ᵐ[μ] g :=
      _root_.HTGeometry.ae_nonneg_of_forall_sq_poly_integral_nonneg
        (by linarith : 0 < ε / 4) hexp hC hgc.aestronglyMeasurable
        (Filter.Eventually.of_forall hbdd) hpoly
    have hpoint := continuous_nonnegative_of_ae hgc hnonneg
    intro x
    rw [← hcancel]
    exact mul_nonneg (Real.exp_pos _).le (hpoint x)
  · intro hpos p
    rw [hform]
    exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hpos x))

end
end RHTower
