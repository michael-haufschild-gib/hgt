import GaloisForLFunctions.HTGeometry.MixedEvenTrigMoments
import GaloisForLFunctions.HTGeometry.MomentInnerProduct

/-!
# Strict positive definiteness of the arcsine Hankel tower

The normalized central-binomial sequence is the moment sequence of `cos² θ` under normalized
Lebesgue measure on the quarter circle.  This module proves the strict, rather than merely
semidefinite, form of that statement.  A nonzero polynomial cannot vanish throughout the quarter
circle: its real root set is finite, whereas `θ ↦ cos² θ` is injective on `(0, π / 2)`.

This is the coercive limit needed by the mass-shifted spectral-face route.  Combined with entrywise
far-right convergence of the shifted Xi moments, it forces every fixed Hankel block to become
positive definite sufficiently far to the right.
-/

open MeasureTheory Polynomial Set
open scoped BigOperators Nat Real Interval

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Squaring preserves injectivity of cosine on the open quarter circle. -/
theorem injOn_cos_sq_Ioo_zero_pi_div_two :
    Set.InjOn (fun x : ℝ => Real.cos x ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
  intro x hx y hy hxy
  have hcx : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨(neg_lt_zero.mpr (by positivity)).trans hx.1, hx.2⟩
  have hcy : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨(neg_lt_zero.mpr (by positivity)).trans hy.1, hy.2⟩
  have hc : Real.cos x = Real.cos y := by nlinarith
  exact Real.injOn_cos
    ⟨hx.1.le, (hx.2.trans (by nlinarith [Real.pi_pos] : Real.pi / 2 < Real.pi)).le⟩
    ⟨hy.1.le, (hy.2.trans (by nlinarith [Real.pi_pos] : Real.pi / 2 < Real.pi)).le⟩ hc

/-- The image of the open quarter circle under `cos²` is infinite. -/
theorem infinite_cos_sq_image_quarter :
    (fun x : ℝ => Real.cos x ^ 2) '' Set.Ioo 0 (Real.pi / 2) |>.Infinite := by
  exact (Set.Ioo_infinite (by positivity : (0 : ℝ) < Real.pi / 2)).image
    injOn_cos_sq_Ioo_zero_pi_div_two

/-- A nonzero polynomial is nonzero after the `cos²` substitution at some point of the open
quarter circle. -/
theorem exists_quarter_eval_cos_sq_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∃ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), p.eval (Real.cos x ^ 2) ≠ 0 := by
  by_contra h
  push Not at h
  have hroot :
      (fun x : ℝ => Real.cos x ^ 2) '' Set.Ioo 0 (Real.pi / 2) ⊆
        {x : ℝ | p.IsRoot x} := by
    rintro y ⟨x, hx, rfl⟩
    exact h x hx
  exact hp (Polynomial.eq_zero_of_infinite_isRoot p
    (Set.Infinite.mono hroot infinite_cos_sq_image_quarter))

/-- A nonzero polynomial square has strictly positive quarter-circle integral after the `cos²`
substitution. -/
theorem integral_quarter_eval_cos_sq_sq_pos {p : Polynomial ℝ} (hp : p ≠ 0) :
    0 < ∫ x in (0 : ℝ)..Real.pi / 2, (p.eval (Real.cos x ^ 2)) ^ 2 := by
  let f : ℝ → ℝ := fun x => (p.eval (Real.cos x ^ 2)) ^ 2
  have hfcont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hfint : IntervalIntegrable f volume (0 : ℝ) (Real.pi / 2) :=
    hfcont.intervalIntegrable _ _
  have hfnn : ∀ x, 0 ≤ f x := fun x => sq_nonneg _
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall hfnn) hfint]
  refine ⟨by positivity, ?_⟩
  let W : Set ℝ := Set.Ioo (0 : ℝ) (Real.pi / 2) ∩ {x : ℝ | p.eval (Real.cos x ^ 2) ≠ 0}
  have hWopen : IsOpen W := by
    exact isOpen_Ioo.inter (isOpen_ne.preimage (p.continuous.comp
      (Real.continuous_cos.pow 2)))
  have hWne : W.Nonempty := by
    obtain ⟨x, hx, hpx⟩ := exists_quarter_eval_cos_sq_ne_zero hp
    exact ⟨x, hx, hpx⟩
  have hWsub : W ⊆ Function.support f ∩ Set.Ioc (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    exact ⟨Function.mem_support.mpr (pow_ne_zero 2 hx.2), ⟨hx.1.1, hx.1.2.le⟩⟩
  exact (hWopen.measure_pos volume hWne).trans_le (measure_mono hWsub)

/-- The central-binomial moment functional is normalized quarter-circle integration after the
`cos²` substitution. -/
theorem momentFunctional_normalizedCentralBinom_eq_quarterIntegral (p : Polynomial ℝ) :
    _root_.HTGeometry.momentFunctional normalizedCentralBinom p =
      (2 / Real.pi) *
        (∫ x in (0 : ℝ)..Real.pi / 2, p.eval (Real.cos x ^ 2)) := by
  rw [_root_.HTGeometry.momentFunctional_eq_support_sum]
  have heval (x : ℝ) :
      p.eval (Real.cos x ^ 2) =
        ∑ k ∈ p.support, p.coeff k * Real.cos x ^ (2 * k) := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro k _
    rw [← pow_mul]
  rw [intervalIntegral.integral_congr (fun x _ => heval x)]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul,
      integral_cos_pow_even_zero_pi_div_two]
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    field_simp [hpi]
  · intro k _
    exact (Real.continuous_cos.pow (2 * k)).const_mul _ |>.intervalIntegrable _ _

/-- The normalized central-binomial sequence defines a positive moment form on all nonzero real
polynomials. -/
theorem normalizedCentralBinom_positiveMomentForm :
    _root_.HTGeometry.PositiveMomentForm normalizedCentralBinom := by
  refine ⟨fun p hp => ?_⟩
  rw [_root_.HTGeometry.momentInner_self,
    momentFunctional_normalizedCentralBinom_eq_quarterIntegral]
  simp only [Polynomial.eval_pow]
  exact mul_pos (div_pos (by norm_num) Real.pi_pos)
    (integral_quarter_eval_cos_sq_sq_pos hp)

/-- Every finite Hankel block of the normalized central-binomial (arcsine) moments is strictly
positive definite. -/
theorem normalizedCentralBinom_momentHankelMatrix_posDef (n : ℕ) :
    (_root_.HTGeometry.momentHankelMatrix normalizedCentralBinom n).PosDef :=
  _root_.HTGeometry.positiveMomentForm_iff_momentHankelMatrix_posDef.mp
    normalizedCentralBinom_positiveMomentForm n

/-- Every finite arcsine Hankel determinant is strictly positive. -/
theorem normalizedCentralBinom_momentHankelMatrix_det_pos (n : ℕ) :
    0 < (_root_.HTGeometry.momentHankelMatrix normalizedCentralBinom n).det :=
  (normalizedCentralBinom_momentHankelMatrix_posDef n).det_pos

end

end GaloisForLFunctions.HTGeometry
