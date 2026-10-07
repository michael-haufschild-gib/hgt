import GaloisForLFunctions.RHTower.XiSignedFactorZeroSeparation
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Analytic roots of the signed Xi factors on the critical strip

The positive-kernel endpoint chord gives the sharp bound `‖xi s‖ ≤ 1/2`
on the closed critical strip. Both signed source factors consequently stay
in the right half-plane and have explicit nonvanishing analytic square roots.
This locates their global square-class obstructions outside the RH domain;
it does not constrain the real parts of Xi zeros within that domain.
-/

open Complex MeasureTheory
namespace RHTower.XiGlobalKummer
open DeBruijn

private theorem kernel_exp_integrable (t : ℝ) :
    Integrable (fun x : ℝ => riemannKernelReal x * Real.exp ((t - 1 / 2) * x)) := by
  refine (riemannKernel_superExp.integrable_mul_exp |t - 1 / 2|).mono'
    ((riemannKernel_superExp.continuous.mul (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _))]
  apply mul_le_mul_of_nonneg_left _ (riemannKernelReal_pos x).le
  apply Real.exp_le_exp.mpr
  simpa only [abs_mul] using le_abs_self ((t - 1 / 2) * x)

private theorem xi_real_eq_integral (t : ℝ) :
    (xi (t : ℂ)).re = ∫ x : ℝ, riemannKernelReal x * Real.exp ((t - 1 / 2) * x) := by
  have h : xi (t : ℂ) =
      ((∫ x : ℝ, riemannKernelReal x * Real.exp ((t - 1 / 2) * x) : ℝ) : ℂ) := by
    rw [xi_eq_positive_bilateral_integral, ← integral_complex_ofReal]
    congr 1
    funext x
    push_cast
    rfl
  rw [h, Complex.ofReal_re]

/-- The endpoint chord of the positive kernel bounds Xi on the real unit interval. -/
theorem xi_real_le_half_of_mem_unit {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (xi (t : ℂ)).re ≤ 1 / 2 := by
  have hpoint (x : ℝ) :
      riemannKernelReal x * Real.exp ((t - 1 / 2) * x) ≤
        (1 - t) * (riemannKernelReal x * Real.exp ((0 - 1 / 2) * x)) +
          t * (riemannKernelReal x * Real.exp ((1 - 1 / 2) * x)) := by
    have hc := convexOn_exp.2 (Set.mem_univ (-(x / 2)))
      (Set.mem_univ (x / 2)) (sub_nonneg.mpr h1) h0 (by ring : 1 - t + t = 1)
    have he : (1 - t) • (-(x / 2)) + t • (x / 2) = (t - 1 / 2) * x := by
      simp only [smul_eq_mul]
      ring
    rw [he] at hc
    have hm := mul_le_mul_of_nonneg_left hc (riemannKernelReal_pos x).le
    simp only [smul_eq_mul] at hm
    rw [show -(x / 2) = (0 - 1 / 2) * x by ring,
      show x / 2 = (1 - 1 / 2) * x by ring] at hm
    nlinarith [hm]
  rw [xi_real_eq_integral]
  calc
    _ ≤ ∫ x : ℝ, (1 - t) * (riemannKernelReal x * Real.exp ((0 - 1 / 2) * x)) +
        t * (riemannKernelReal x * Real.exp ((1 - 1 / 2) * x)) :=
      integral_mono (kernel_exp_integrable t)
        (((kernel_exp_integrable 0).const_mul (1 - t)).add
          ((kernel_exp_integrable 1).const_mul t)) hpoint
    _ = (1 - t) * (xi (0 : ℂ)).re + t * (xi (1 : ℂ)).re := by
      rw [integral_add ((kernel_exp_integrable 0).const_mul (1 - t))
        ((kernel_exp_integrable 1).const_mul t), integral_const_mul, integral_const_mul,
        ← xi_real_eq_integral, ← xi_real_eq_integral]
      norm_num
    _ = 1 / 2 := by rw [xi_zero, xi_one]; norm_num; ring

/-- Uniform sharp bound on the closed critical strip. -/
theorem norm_xi_le_half_of_closed_strip {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ‖xi s‖ ≤ 1 / 2 :=
  (norm_xi_le_real_axis s).trans (xi_real_le_half_of_mem_unit h0 h1)

def criticalStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1}

private theorem norm_weighted_xi_le_half {n : ℕ} (hn : 1 ≤ n) {s : ℂ}
    (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ‖Complex.exp (-s * (Real.log n : ℂ)) * xi s‖ ≤ 1 / 2 := by
  have he : ‖Complex.exp (-s * (Real.log n : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h0)
      (Real.log_nonneg (by exact_mod_cast hn))
  calc
    _ = ‖Complex.exp (-s * (Real.log n : ℂ))‖ * ‖xi s‖ := norm_mul _ _
    _ ≤ 1 * (1 / 2) := mul_le_mul he (norm_xi_le_half_of_closed_strip h0 h1)
      (norm_nonneg _) (by norm_num)
    _ = 1 / 2 := one_mul _

theorem deletionFactor_re_ge_half {n : ℕ} (hn : 1 ≤ n) {s : ℂ}
    (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) : 1 / 2 ≤ (deletionFactor n s).re := by
  have hb := (Complex.re_le_norm (Complex.exp (-s * (Real.log n : ℂ)) * xi s)).trans
    (norm_weighted_xi_le_half hn h0 h1)
  simp only [deletionFactor, Complex.sub_re, Complex.one_re]
  linarith

theorem augmentationFactor_re_ge_half {n : ℕ} (hn : 1 ≤ n) {s : ℂ}
    (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) : 1 / 2 ≤ (augmentationFactor n s).re := by
  have hb := (Complex.re_le_norm (-(Complex.exp (-s * (Real.log n : ℂ)) * xi s))).trans
    (by simpa only [norm_neg] using norm_weighted_xi_le_half hn h0 h1)
  simp only [Complex.neg_re] at hb
  change 1 / 2 ≤ 2 - (1 - (Complex.exp (-s * (Real.log n : ℂ)) * xi s).re)
  linarith

private theorem analytic_root_of_re_pos {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hpos : ∀ s ∈ U, 0 < (f s).re) :
    AnalyticOnNhd ℂ (fun s => Complex.exp (Complex.log (f s) / 2)) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro s hs
  exact (((Complex.differentiableAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl (hpos s hs)))).comp
    s (hf s hs).differentiableAt).div_const 2).cexp.differentiableWithinAt

private theorem exp_half_log_sq {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (Complex.log z / 2) ^ 2 = z := by
  rw [← Complex.exp_nat_mul]
  change Complex.exp (2 * (Complex.log z / 2)) = z
  rw [show (2 : ℂ) * (Complex.log z / 2) = Complex.log z by ring]
  exact Complex.exp_log hz

noncomputable def deletionStripRoot (n : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (Complex.log (deletionFactor n s) / 2)

noncomputable def augmentationStripRoot (n : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (Complex.log (augmentationFactor n s) / 2)

theorem deletionStripRoot_ne_zero (n : ℕ) (s : ℂ) : deletionStripRoot n s ≠ 0 :=
  Complex.exp_ne_zero _

theorem augmentationStripRoot_ne_zero (n : ℕ) (s : ℂ) : augmentationStripRoot n s ≠ 0 :=
  Complex.exp_ne_zero _

theorem deletionStripRoot_analytic {n : ℕ} (hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (deletionStripRoot n) criticalStrip := by
  apply analytic_root_of_re_pos
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const))
    (fun s _ => (deletionFactor_differentiable n).analyticAt s)
  intro s hs
  exact lt_of_lt_of_le (by norm_num) (deletionFactor_re_ge_half hn hs.1.le hs.2.le)

theorem augmentationStripRoot_analytic {n : ℕ} (hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (augmentationStripRoot n) criticalStrip := by
  apply analytic_root_of_re_pos
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const))
    (fun s _ => (augmentationFactor_differentiable n).analyticAt s)
  intro s hs
  exact lt_of_lt_of_le (by norm_num) (augmentationFactor_re_ge_half hn hs.1.le hs.2.le)

theorem deletionStripRoot_sq {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : s ∈ criticalStrip) :
    deletionStripRoot n s ^ 2 = deletionFactor n s := by
  apply exp_half_log_sq
  intro hz
  have h := deletionFactor_re_ge_half hn hs.1.le hs.2.le
  rw [hz, Complex.zero_re] at h
  norm_num at h

theorem augmentationStripRoot_sq {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : s ∈ criticalStrip) :
    augmentationStripRoot n s ^ 2 = augmentationFactor n s := by
  apply exp_half_log_sq
  intro hz
  have h := augmentationFactor_re_ge_half hn hs.1.le hs.2.le
  rw [hz, Complex.zero_re] at h
  norm_num at h

end RHTower.XiGlobalKummer
