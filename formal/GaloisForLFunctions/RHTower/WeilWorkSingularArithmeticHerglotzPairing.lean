import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticCauchyReflection
import GaloisForLFunctions.RHTower.WeilFullConeHorizontalPotential

/-!
# Pairing a Weil source with a reflected holomorphic test

The regularized Herglotz kernel is integrable jointly against a fourth-order
decaying test and the source boundary measure. Its real pairing is exactly
the critical-line evaluation. The regularizing terms are retained until
after Fubini; their separate measure integrals need not exist.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

noncomputable section

namespace RHTower.WeilSingularArithmetic

theorem norm_herglotzKernel_quarter_le (t r : ℝ) :
    ‖WeilSpectral.herglotzKernel ((1 / 4 : ℂ) + t * I) r‖ ≤
      (40 * (1 + t ^ 2)) * (1 + r ^ 2)⁻¹ := by
  have hz : ‖(1 / 4 : ℂ) + t * I‖ ≤ 1 + |t| := by
    calc ‖(1 / 4 : ℂ) + t * I‖ ≤ ‖(1 / 4 : ℂ)‖ + ‖(t : ℂ) * I‖ :=
        norm_add_le _ _
      _ ≤ 1 + |t| := by norm_num [norm_mul]
  refine (WeilSpectral.norm_herglotzKernel_le (c := 1 / 4)
    (by norm_num) (by simp) hz r).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  nlinarith [sq_nonneg (|t| - 1), sq_abs t]

private theorem decay_bound {u C t : ℝ} (hu : 0 ≤ u)
    (h : u * (1 + t ^ 2) ^ 2 ≤ C) : u ≤ C * (1 + t ^ 2)⁻¹ := by
  rw [le_mul_inv_iff₀ (by positivity : 0 < 1 + t ^ 2)]
  exact (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg t] :
    1 + t ^ 2 ≤ (1 + t ^ 2) ^ 2) hu).trans h

theorem integrable_herglotzKernel_mul_test {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {f : ℝ → ℂ} {C : ℝ} (hf : Continuous f)
    (hdec : ∀ t, ‖f t‖ * (1 + t ^ 2) ^ 2 ≤ C) :
    Integrable (fun tr : ℝ × ℝ =>
      WeilSpectral.herglotzKernel ((1 / 4 : ℂ) + tr.1 * I) tr.2 * f tr.1)
      (volume.prod (WeilSpectral.boundaryMeasure hW)) := by
  have hmaj := (_root_.integrable_inv_one_add_sq.mul_prod
    (WeilSpectral.integrable_inv_one_add_sq hW)).const_mul (40 * C)
  refine hmaj.mono' ?_ (Eventually.of_forall fun tr => ?_)
  · apply Measurable.aestronglyMeasurable
    unfold WeilSpectral.herglotzKernel
    exact (by fun_prop : Measurable fun tr : ℝ × ℝ =>
      (1 / ((1 / 4 : ℂ) + tr.1 * I - I * tr.2) -
        I * tr.2 / (1 + (tr.2 : ℂ) ^ 2)) * f tr.1)
  · rw [norm_mul]
    have hD : 0 < 1 + tr.1 ^ 2 := by positivity
    calc ‖WeilSpectral.herglotzKernel ((1 / 4 : ℂ) + tr.1 * I) tr.2‖ * ‖f tr.1‖
        ≤ (40 * (1 + tr.1 ^ 2) * (1 + tr.2 ^ 2)⁻¹) * ‖f tr.1‖ :=
          mul_le_mul_of_nonneg_right (norm_herglotzKernel_quarter_le _ _) (norm_nonneg _)
      _ = (40 * (‖f tr.1‖ * (1 + tr.1 ^ 2) ^ 2)) *
          ((1 + tr.1 ^ 2)⁻¹ * (1 + tr.2 ^ 2)⁻¹) := by
        field_simp
      _ ≤ (40 * C) * ((1 + tr.1 ^ 2)⁻¹ * (1 + tr.2 ^ 2)⁻¹) := by
        gcongr
        exact hdec tr.1

theorem im_integral_eq_zero_of_conj_neg {f : ℝ → ℂ}
    (hsym : ∀ t, f (-t) = conj (f t)) : (∫ t, f t).im = 0 := by
  have h := integral_neg_eq_self f volume
  simp_rw [hsym] at h
  rw [integral_conj] at h
  have hi := congrArg Complex.im h
  simp only [conj_im] at hi
  linarith

theorem integrable_quarter_cauchy {f : ℝ → ℂ} (hf : Integrable f) (r : ℝ) :
    Integrable (fun t => f t / ((1 / 4 : ℂ) + (t - r) * I)) := by
  refine (hf.norm.const_mul 4).mono' (hf.aestronglyMeasurable.div₀ (by fun_prop))
    (Eventually.of_forall fun t => ?_)
  have hd : (1 / 4 : ℝ) ≤ ‖(1 / 4 : ℂ) + (t - r) * I‖ := by
    simpa using Complex.re_le_norm ((1 / 4 : ℂ) + (t - r) * I)
  rw [norm_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hd)]
  nlinarith [mul_le_mul_of_nonneg_left hd (norm_nonneg (f t))]

/-- Fourth-order line decay makes the actual source pairing integrable. -/
theorem integrable_weilContinuation_mul_line_test {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {v : ℝ → ℂ} {C : ℝ} (hv : Continuous v)
    (hdec : ∀ t, ‖v t‖ * (1 + t ^ 2) ^ 2 ≤ C) :
    Integrable (fun t : ℝ => WeilSpectral.weilContinuation hW ((3 / 4 : ℂ) + t * I) * v t) := by
  haveI := WeilSpectral.sFinite_boundaryMeasure hW
  have hjoint := integrable_herglotzKernel_mul_test hW hv hdec
  have hHi : Integrable (fun t : ℝ =>
      WeilSpectral.herglotzFunction hW ((1 / 4 : ℂ) + t * I) * v t) := by
    simpa only [WeilSpectral.herglotzFunction, integral_mul_const] using hjoint.integral_prod_left
  have hvi : Integrable v := (_root_.integrable_inv_one_add_sq.const_mul C).mono'
    hv.aestronglyMeasurable (Eventually.of_forall fun t => decay_bound (norm_nonneg _) (hdec t))
  refine (hHi.add (hvi.const_mul
    (WeilHerglotz.weilFunction lam 2 - WeilSpectral.herglotzFunction hW (2 - 1 / 2)))).congr
      (Eventually.of_forall fun t => ?_)
  dsimp only [Pi.add_apply]
  unfold WeilSpectral.weilContinuation
  rw [show (3 / 4 : ℂ) + t * I - 1 / 2 = (1 / 4 : ℂ) + t * I by ring]
  exact (add_mul _ _ _).symm

/-- The source pairing evaluates the test on the critical line. -/
theorem re_integral_weilContinuation_mul_test_eq {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {f : ℂ → ℂ} {C : ℝ}
    (hf : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → DifferentiableAt ℂ f s)
    (hsym : ∀ t : ℝ, f ((1 / 4 : ℂ) + t * I) =
      conj (f ((3 / 4 : ℂ) + t * I)))
    (hbar : ∀ t : ℝ, f ((3 / 4 : ℂ) + (-t) * I) =
      conj (f ((3 / 4 : ℂ) + t * I)))
    (hdec : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 →
      ‖f s‖ * (1 + s.im ^ 2) ^ 2 ≤ C) :
    (∫ t : ℝ, WeilSpectral.weilContinuation hW ((3 / 4 : ℂ) + t * I) *
      f ((3 / 4 : ℂ) + t * I)).re =
      Real.pi * ∫ r : ℝ, (f ((1 / 2 : ℂ) + r * I)).re
        ∂WeilSpectral.boundaryMeasure hW := by
  haveI := WeilSpectral.sFinite_boundaryMeasure hW
  let v : ℝ → ℂ := fun t => f ((3 / 4 : ℂ) + t * I)
  have hv : Continuous v := continuous_iff_continuousAt.mpr fun t =>
    (hf _ (by norm_num) (by simp)).continuousAt.comp (by fun_prop)
  have hvdec (t : ℝ) : ‖v t‖ * (1 + t ^ 2) ^ 2 ≤ C := by
    simpa [v] using hdec ((3 / 4 : ℂ) + t * I) (by norm_num) (by simp)
  have hvi : Integrable v := (_root_.integrable_inv_one_add_sq.const_mul C).mono'
    hv.aestronglyMeasurable (Eventually.of_forall fun t => decay_bound (norm_nonneg _) (hvdec t))
  have him : (∫ t, v t).im = 0 := im_integral_eq_zero_of_conj_neg (by simpa [v] using hbar)
  have hjoint := integrable_herglotzKernel_mul_test hW hv hvdec
  have hinner (r : ℝ) :
      (∫ t : ℝ, WeilSpectral.herglotzKernel ((1 / 4 : ℂ) + t * I) r * v t).re =
        Real.pi * (f ((1 / 2 : ℂ) + r * I)).re := by
    have heq (t : ℝ) : WeilSpectral.herglotzKernel ((1 / 4 : ℂ) + t * I) r * v t =
        v t / ((1 / 4 : ℂ) + (t - r) * I) -
          (I * r / (1 + (r : ℂ) ^ 2)) * v t := by
      unfold WeilSpectral.herglotzKernel
      have hd : (1 / 4 : ℂ) + t * I - I * r = (1 / 4 : ℂ) + (t - r) * I := by ring
      rw [hd]
      ring
    simp_rw [heq]
    rw [integral_sub (integrable_quarter_cauchy hvi r) (hvi.const_mul _), integral_const_mul]
    have hc : I * (r : ℂ) / (1 + (r : ℂ) ^ 2) = ((r / (1 + r ^ 2) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [hc, Complex.sub_re, Complex.mul_re, Complex.mul_re, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_mul, add_zero, sub_zero, him]
    exact re_integral_reflected_cauchy hf hsym
      (fun s hs1 hs2 => decay_bound (norm_nonneg _) (hdec s hs1 hs2)) r
  have hHi : Integrable (fun t : ℝ =>
      WeilSpectral.herglotzFunction hW ((1 / 4 : ℂ) + t * I) * v t) := by
    simpa only [WeilSpectral.herglotzFunction, integral_mul_const] using hjoint.integral_prod_left
  have hswap :
      (∫ t : ℝ, WeilSpectral.herglotzFunction hW ((1 / 4 : ℂ) + t * I) * v t) =
        ∫ r, (∫ t : ℝ, WeilSpectral.herglotzKernel ((1 / 4 : ℂ) + t * I) r * v t)
          ∂WeilSpectral.boundaryMeasure hW := by
    simpa only [WeilSpectral.herglotzFunction, integral_mul_const] using
      integral_integral_swap (f := fun (t r : ℝ) =>
        WeilSpectral.herglotzKernel ((1 / 4 : ℂ) + t * I) r * v t) hjoint
  let k := WeilHerglotz.weilFunction lam 2 - WeilSpectral.herglotzFunction hW (2 - 1 / 2)
  have hk : k.re = 0 := by
    dsimp [k]
    rw [WeilSpectral.re_herglotzFunction_eq hW (by norm_num)]
    ring
  have hsource (t : ℝ) : WeilSpectral.weilContinuation hW ((3 / 4 : ℂ) + t * I) * v t =
      WeilSpectral.herglotzFunction hW ((1 / 4 : ℂ) + t * I) * v t + k * v t := by
    unfold WeilSpectral.weilContinuation
    rw [show (3 / 4 : ℂ) + t * I - 1 / 2 = (1 / 4 : ℂ) + t * I by ring]
    exact add_mul _ _ _
  change (∫ t : ℝ, WeilSpectral.weilContinuation hW ((3 / 4 : ℂ) + t * I) * v t).re = _
  simp_rw [hsource]
  rw [integral_add hHi (hvi.const_mul k), integral_const_mul, Complex.add_re,
    Complex.mul_re, hk, him, zero_mul, mul_zero, sub_zero, add_zero, hswap]
  rw [← RCLike.re_eq_complex_re, ← integral_re hjoint.integral_prod_right]
  simp_rw [show ∀ z : ℂ, RCLike.re z = z.re from fun _ => rfl, hinner]
  exact integral_const_mul _ _

end RHTower.WeilSingularArithmetic
