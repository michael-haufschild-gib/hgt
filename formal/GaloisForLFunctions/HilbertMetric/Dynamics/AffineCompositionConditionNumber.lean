import GaloisForLFunctions.RHTower.BakerGeneralProof.FrequencyModulus
import GaloisForLFunctions.HTGeometry.ClogVertLog

/-!
# Conditioning of affine disk composition on a finite coefficient window

For the disk symbol `1-p+pz`, the coefficient matrix of Charpentier–Zarouf
(arXiv:2611.17392, Theorem 1.7) consists of binomial rows. In the Wiener
norm, the forward map is contractive for `0 ≤ p ≤ 1`. In degree at most
`d` the inverse amplifies errors by exactly `(2/p-1)^d`. This quantifies
the price of expanding the imaginary parts of polynomial roots by `1/p`.
-/
noncomputable section
open Polynomial Complex
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.BakerGeneralProof

namespace GaloisForLFunctions.HilbertMetric.Dynamics.AffineComposition

/-- The affine chart fixing the boundary point one. -/
def chart (p : ℝ) : ℂ[X] := C (p : ℂ) * X + C ((1-p : ℝ) : ℂ)

private theorem norm_C (a : ℂ) : coeffNormSum (C a) = ‖a‖ := by
  simpa using coeffNormSum_monomial 0 a

private theorem norm_C_mul_X (a : ℂ) : coeffNormSum (C a * X) = ‖a‖ := by
  simpa [← Polynomial.C_mul_X_pow_eq_monomial] using coeffNormSum_monomial 1 a

theorem chart_comp (p q : ℝ) : (chart p).comp (chart q) = chart (p*q) := by
  simp only [chart, add_comp, mul_comp, C_comp, X_comp]
  push_cast
  simp only [map_mul, map_sub, map_one]
  ring

private theorem chart_one : chart 1 = X := by simp [chart]

private theorem gain_le_of_chart (p : ℝ) : coeffNormSum (chart p) ≤ |p| + |1-p| := by
  refine (coeffNormSum_add_le (C (p : ℂ) * X) (C ((1-p : ℝ) : ℂ))).trans_eq ?_
  rw [norm_C_mul_X, norm_C, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

private theorem boundary_attainment (p : ℝ) :
    ∃ z : ℂ, ‖z‖ ≤ 1 ∧ ‖(chart p).eval z‖ = |p| + |1-p| := by
  have hminus : (chart p).eval (-1) = ((1-2*p : ℝ) : ℂ) := by
    simp only [chart, eval_add, eval_mul, eval_C, eval_X]
    push_cast
    ring
  rcases le_or_gt p 0 with hp | hp
  · refine ⟨-1, by simp, ?_⟩
    rw [hminus, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1-2*p),
      abs_of_nonpos hp, abs_of_nonneg (by linarith : 0 ≤ 1-p)]
    ring
  rcases le_or_gt p 1 with h1 | h1
  · refine ⟨1, by simp, ?_⟩
    rw [show (chart p).eval 1 = 1 by simp [chart], norm_one, abs_of_pos hp,
      abs_of_nonneg (sub_nonneg.mpr h1)]
    ring
  · refine ⟨-1, by simp, ?_⟩
    rw [hminus, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : 1-2*p ≤ 0),
      abs_of_pos hp, abs_of_nonpos (by linarith : 1-p ≤ 0)]
    ring

/-- Every monomial attains the exact coefficient gain of its binomial row. -/
theorem norm_chart_pow (p : ℝ) (d : ℕ) :
    coeffNormSum (chart p ^ d) = (|p|+|1-p|)^d := by
  refine le_antisymm ((coeffNormSum_pow_le _ _).trans
    (pow_le_pow_left₀ (coeffNormSum_nonneg _) (gain_le_of_chart p) d)) ?_
  obtain ⟨z, hz, he⟩ := boundary_attainment p
  simpa only [eval_pow, norm_pow, he, coeffNormSum] using
    norm_polyEval_le_of_norm_le_one (chart p ^ d) hz

/-- Composition bound with the sharp constant on the whole degree window. -/
theorem norm_comp_chart (P : ℂ[X]) (p : ℝ) (d : ℕ) (hd : P.natDegree ≤ d) :
    coeffNormSum (P.comp (chart p)) ≤ (|p| + |1-p|)^d * coeffNormSum P := by
  have hg : 1 ≤ |p|+|1-p| := by
    simpa only [show p+(1-p) = 1 by ring, abs_one] using abs_add_le p (1-p)
  have hform : P.comp (chart p) = ∑ k ∈ P.support, C (P.coeff k) * chart p ^ k := by
    conv_lhs => rw [P.as_sum_support, Polynomial.sum_comp]
    simp only [monomial_comp]
  rw [hform, coeffNormSum_eq_sum_support P, Finset.mul_sum]
  refine (coeffNormSum_finset_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  calc coeffNormSum (C (P.coeff k) * chart p ^ k)
      ≤ coeffNormSum (C (P.coeff k)) * coeffNormSum (chart p ^ k) := coeffNormSum_mul_le _ _
    _ ≤ _ := by
      rw [norm_C, norm_chart_pow, mul_comm ‖_‖]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hg
        ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)).trans hd)) (norm_nonneg _)

/-- Bounded disk composition is a contraction, uniformly in the degree. -/
theorem disk_contraction (P : ℂ[X]) {p : ℝ} (hp : 0 ≤ p) (h1 : p ≤ 1) :
    coeffNormSum (P.comp (chart p)) ≤ coeffNormSum P := by
  have hg : |p|+|1-p| = 1 := by rw [abs_of_nonneg hp, abs_of_nonneg (sub_nonneg.mpr h1)]; ring
  simpa [hg] using norm_comp_chart P p P.natDegree le_rfl

/-- Composition by the reciprocal slope exactly reconstructs every polynomial. -/
theorem inverse_chart (P : ℂ[X]) {p : ℝ} (hp : p ≠ 0) :
    (P.comp (chart p)).comp (chart p⁻¹) = P := by
  rw [comp_assoc, chart_comp, mul_inv_cancel₀ hp, chart_one, comp_X]

private theorem natDegree_chart_le (p : ℝ) : (chart p).natDegree ≤ 1 := by
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_C_mul_le ..).trans natDegree_X_le
  · simp

/-- The smallest Lipschitz constant of inversion in degree at most `d`. -/
theorem inverse_bound_iff {p : ℝ} (hp : 0 < p) (h1 : p ≤ 1) (d : ℕ) (K : ℝ) :
    (∀ P : ℂ[X], P.natDegree ≤ d →
      coeffNormSum P ≤ K * coeffNormSum (P.comp (chart p))) ↔ (2/p-1)^d ≤ K := by
  have hi : 1 ≤ p⁻¹ := (one_le_inv₀ hp).mpr h1
  have hg : |p⁻¹|+|1-p⁻¹| = 2/p-1 := by
    rw [abs_of_pos (inv_pos.mpr hp), abs_of_nonpos (sub_nonpos.mpr hi)]
    ring
  have hdg (f : ℂ[X]) (a : ℝ) : (f.comp (chart a)).natDegree ≤ f.natDegree := by
    exact natDegree_comp_le.trans ((Nat.mul_le_mul_left _ (natDegree_chart_le a)).trans_eq (Nat.mul_one _))
  constructor
  · intro h
    have he := h ((X^d : ℂ[X]).comp (chart p⁻¹))
      ((hdg _ _).trans (natDegree_X_pow_le _))
    rw [comp_assoc, chart_comp, inv_mul_cancel₀ hp.ne', chart_one, comp_X, pow_comp, X_comp,
      norm_chart_pow, hg] at he
    have hm : coeffNormSum (X^d : ℂ[X]) = 1 := by
      simpa [← C_mul_X_pow_eq_monomial] using coeffNormSum_monomial d (1 : ℂ)
    simpa [hm] using he
  · intro h P hd
    have hb := norm_comp_chart (P.comp (chart p)) p⁻¹ d ((hdg _ _).trans hd)
    rw [inverse_chart P hp.ne', hg] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right h (coeffNormSum_nonneg _))

/-- A uniform inverse bound over growing degree windows is equivalent to
boundedness of the degree times the excess root-height amplification. -/
theorem uniform_inverse_iff (p : ℕ → ℝ) (hp : ∀ d, 0 < p d) (h1 : ∀ d, p d ≤ 1) :
    (∃ K : ℝ, ∀ d (P : ℂ[X]), P.natDegree ≤ d →
      coeffNormSum P ≤ K * coeffNormSum (P.comp (chart (p d)))) ↔
    ∃ B : ℝ, ∀ d : ℕ, d*((p d)⁻¹-1) ≤ B := by
  have hpos (d : ℕ) : 0 ≤ (p d)⁻¹-1 := sub_nonneg.mpr ((one_le_inv₀ (hp d)).mpr (h1 d))
  have hbase (d : ℕ) : 2/p d-1 = 1+2*((p d)⁻¹-1) := by ring
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨(K-1)/2, fun d => ?_⟩
    have he := (inverse_bound_iff (hp d) (h1 d) d K).mp (hK d)
    rw [hbase] at he
    have hb := one_add_mul_le_pow (a := 2*((p d)⁻¹-1)) (by linarith only [hpos d]) d
    linarith only [hb.trans he]
  · rintro ⟨B, hB⟩
    refine ⟨Real.exp (2*B), fun d => (inverse_bound_iff (hp d) (h1 d) d _).mpr ?_⟩
    rw [hbase]
    calc (1+2*((p d)⁻¹-1))^d ≤ (Real.exp (2*((p d)⁻¹-1)))^d :=
           pow_le_pow_left₀ (by linarith only [hpos d])
             (by simpa only [add_comm] using Real.add_one_le_exp (2*((p d)⁻¹-1))) _
         _ = Real.exp (d*(2*((p d)⁻¹-1))) := (Real.exp_nat_mul _ _).symm
         _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hB d])

/-- Under the affine chart each root height is multiplied by exactly
`1/p`. The bound is valid for all roots, including the extreme ones. -/
theorem root_height_window (P : ℂ[X]) {p : ℝ} (hp : 0 < p) (B : ℝ) :
    (∀ z : ℂ, (P.comp (chart p)).IsRoot z → z.im ≤ B/p) ↔
    ∀ z : ℂ, P.IsRoot z → z.im ≤ B := by
  let f (z : ℂ) := (p : ℂ)*z+((1-p : ℝ) : ℂ)
  have hroot (z : ℂ) : (P.comp (chart p)).IsRoot z ↔ P.IsRoot (f z) := by
    simp only [Polynomial.IsRoot, eval_comp, chart, eval_add, eval_mul, eval_C, eval_X, f]
  have him (z : ℂ) : (f z).im = p*z.im := by simp [f, Complex.mul_im]
  have hsurj : Function.Surjective f := by
    intro z
    refine ⟨(z-((1-p : ℝ) : ℂ))/(p : ℂ), ?_⟩
    dsimp [f]
    field_simp [Complex.ofReal_ne_zero.mpr hp.ne']
    ring
  constructor
  · intro h z hz
    obtain ⟨w, rfl⟩ := hsurj z
    rw [him, mul_comm]
    exact (le_div_iff₀ hp).mp (h w ((hroot w).mpr hz))
  · intro h z hz
    apply (le_div_iff₀ hp).mpr
    rw [mul_comm, ← him]
    exact h _ ((hroot z).mp hz)

#print axioms chart_comp
#print axioms norm_chart_pow
#print axioms norm_comp_chart
#print axioms disk_contraction
#print axioms inverse_chart
#print axioms inverse_bound_iff
#print axioms uniform_inverse_iff
#print axioms root_height_window
end GaloisForLFunctions.HilbertMetric.Dynamics.AffineComposition
