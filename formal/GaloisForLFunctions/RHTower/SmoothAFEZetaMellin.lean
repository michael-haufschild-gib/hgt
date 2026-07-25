import GaloisForLFunctions.RHTower.SmoothAFEGaussianResidueCrossing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries

/-!
# Absolute-half-plane zeta Mellin expansion for the smooth AFE

This module supplies the first zeta-dependent step of the smooth approximate functional equation.
On a positive line `Re w = c` with `1 < Re s + c`, the zeta-weighted Gaussian Mellin integrand

`ζ(s + w) x^w exp(w²) / w`

is absolutely integrable.  Expanding zeta by its convergent Dirichlet series is justified term by
term, and Bochner integration commutes with the resulting infinite sum by an explicit
`p`-series times Gaussian majorant.

No analytic continuation estimate, functional equation, or asymptotic hypothesis is used here.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory

def smoothAFEZetaMajorant (p : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ p

def smoothAFEZetaMellinIntegrand (s : ℂ) (x : ℝ) (w : ℂ) : ℂ :=
  riemannZeta (s + w) * (x : ℂ) ^ w * smoothAFEGaussianKernel w

def smoothAFEZetaMellinTerm (s : ℂ) (x : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  (1 / (n + 1 : ℂ) ^ (s + w)) * (x : ℂ) ^ w * smoothAFEGaussianKernel w

theorem summable_smoothAFEZetaMajorant {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ p) := by
  have h := Real.summable_one_div_nat_rpow.mpr hp
  have h' := (summable_nat_add_iff 1).2 h
  simpa only [Nat.cast_add, Nat.cast_one] using h'

theorem norm_riemannZeta_vertical_le_smoothAFEZetaMajorant
    {s : ℂ} {c : ℝ} (hsc : 1 < s.re + c) (t : ℝ) :
    ‖riemannZeta (s + ((c : ℂ) + (t : ℂ) * I))‖
      ≤ smoothAFEZetaMajorant (s.re + c) := by
  have hre : (s + ((c : ℂ) + (t : ℂ) * I)).re = s.re + c := by simp
  have hz : 1 < (s + ((c : ℂ) + (t : ℂ) * I)).re := by simpa [hre] using hsc
  have hsum0 := Complex.summable_one_div_nat_cpow.mpr hz
  have hsum := (summable_nat_add_iff 1).2 hsum0
  have hsum' : Summable (fun n : ℕ =>
      1 / (n + 1 : ℂ) ^ (s + ((c : ℂ) + (t : ℂ) * I))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsum
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hz]
  calc
    ‖∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (s + ((c : ℂ) + (t : ℂ) * I))‖
        ≤ ∑' n : ℕ, ‖1 / (n + 1 : ℂ) ^ (s + ((c : ℂ) + (t : ℂ) * I))‖ :=
      norm_tsum_le_tsum_norm hsum'.norm
    _ = smoothAFEZetaMajorant (s.re + c) := by
      unfold smoothAFEZetaMajorant
      apply tsum_congr
      intro n
      rw [norm_div, norm_one,
        show (n : ℂ) + 1 = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos
        (by exact_mod_cast Nat.succ_pos n), hre]

theorem norm_smoothAFEZetaMellinIntegrand_vertical_le
    {s : ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hsc : 1 < s.re + c) (t : ℝ) :
    ‖smoothAFEZetaMellinIntegrand s x ((c : ℂ) + (t : ℂ) * I)‖
      ≤ ((smoothAFEZetaMajorant (s.re + c) * x ^ c) *
          (Real.exp (c ^ 2) / c)) * Real.exp (-(t ^ 2)) := by
  rw [smoothAFEZetaMellinIntegrand, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  calc
    ‖riemannZeta (s + (↑c + ↑t * I))‖ * x ^ c *
        ‖smoothAFEGaussianKernel (↑c + ↑t * I)‖
      ≤ smoothAFEZetaMajorant (s.re + c) * x ^ c *
          ((Real.exp (c ^ 2) / c) * Real.exp (-(t ^ 2))) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right
            (norm_riemannZeta_vertical_le_smoothAFEZetaMajorant hsc t)
            (by positivity)
        · exact norm_smoothAFEGaussianKernel_vertical_le hc t
        · exact norm_nonneg _
        · exact mul_nonneg (tsum_nonneg fun _ => by positivity) (by positivity)
    _ = ((smoothAFEZetaMajorant (s.re + c) * x ^ c) *
          (Real.exp (c ^ 2) / c)) * Real.exp (-(t ^ 2)) := by ring

theorem smoothAFEZetaMellinIntegrand_verticalIntegrable
    {s : ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hsc : 1 < s.re + c) :
    Complex.VerticalIntegrable (smoothAFEZetaMellinIntegrand s x) c := by
  rw [Complex.VerticalIntegrable]
  apply Integrable.mono'
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      ((smoothAFEZetaMajorant (s.re + c) * x ^ c) *
        (Real.exp (c ^ 2) / c)))
  · haveI : NeZero (x : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    have hzcont : Continuous (fun t : ℝ =>
        riemannZeta (s + ((c : ℂ) + (t : ℂ) * I))) := by
      rw [continuous_iff_continuousAt]
      intro t
      apply (differentiableAt_riemannZeta ?_).continuousAt.comp
      · fun_prop
      · intro heq
        have hre := congrArg Complex.re heq
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero,
          Complex.one_re] at hre
        linarith
    apply Continuous.aestronglyMeasurable
    exact (hzcont.mul
      ((continuous_const_cpow (x : ℂ)).comp (by fun_prop))).mul
      ((continuous_exp.comp (by fun_prop)).div
        (by fun_prop)
        (fun t hzero => by
          have hre : (((c : ℂ) + (t : ℂ) * I)).re = c := by simp
          rw [← hre] at hc
          exact (hc.ne' (congrArg Complex.re hzero)).elim))
  · exact Filter.Eventually.of_forall fun t => by
      simpa using norm_smoothAFEZetaMellinIntegrand_vertical_le hx hc hsc t

theorem smoothAFEZetaMellinIntegrand_eq_tsum
    {s : ℂ} {x c t : ℝ} (hsc : 1 < s.re + c) :
    smoothAFEZetaMellinIntegrand s x ((c : ℂ) + (t : ℂ) * I)
      = ∑' n : ℕ, smoothAFEZetaMellinTerm s x n ((c : ℂ) + (t : ℂ) * I) := by
  have hre : (s + ((c : ℂ) + (t : ℂ) * I)).re = s.re + c := by simp
  have hz : 1 < (s + ((c : ℂ) + (t : ℂ) * I)).re := by simpa [hre] using hsc
  rw [smoothAFEZetaMellinIntegrand, zeta_eq_tsum_one_div_nat_add_one_cpow hz]
  simp only [smoothAFEZetaMellinTerm, ← tsum_mul_right]

theorem norm_smoothAFEZetaMellinTerm_vertical_le
    {s : ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (n : ℕ) (t : ℝ) :
    ‖smoothAFEZetaMellinTerm s x n ((c : ℂ) + (t : ℂ) * I)‖
      ≤ (((1 / (n + 1 : ℝ) ^ (s.re + c)) * x ^ c) *
          (Real.exp (c ^ 2) / c)) * Real.exp (-(t ^ 2)) := by
  rw [smoothAFEZetaMellinTerm, norm_mul, norm_mul, norm_div, norm_one,
    show (n : ℂ) + 1 = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos
      (by exact_mod_cast Nat.succ_pos n),
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  calc
    1 / (n + 1 : ℝ) ^ (s.re + c) * x ^ c *
        ‖smoothAFEGaussianKernel (↑c + ↑t * I)‖
      ≤ 1 / (n + 1 : ℝ) ^ (s.re + c) * x ^ c *
          ((Real.exp (c ^ 2) / c) * Real.exp (-(t ^ 2))) := by
        apply mul_le_mul_of_nonneg_left
          (norm_smoothAFEGaussianKernel_vertical_le hc t)
        positivity
    _ = (((1 / (n + 1 : ℝ) ^ (s.re + c)) * x ^ c) *
          (Real.exp (c ^ 2) / c)) * Real.exp (-(t ^ 2)) := by ring

theorem smoothAFEZetaMellinTerm_verticalIntegrable
    {s : ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (n : ℕ) :
    Integrable (fun t : ℝ =>
      smoothAFEZetaMellinTerm s x n ((c : ℂ) + (t : ℂ) * I)) := by
  apply Integrable.mono'
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      (((1 / (n + 1 : ℝ) ^ (s.re + c)) * x ^ c) *
        (Real.exp (c ^ 2) / c)))
  · haveI : NeZero (x : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    letI : NeZero (n + 1 : ℂ) := ⟨hn⟩
    have hpowN : Continuous (fun t : ℝ =>
        (n + 1 : ℂ) ^ (s + ((c : ℂ) + (t : ℂ) * I))) :=
      (continuous_const_cpow (n + 1 : ℂ)).comp (by fun_prop)
    have hpowX : Continuous (fun t : ℝ =>
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) :=
      (continuous_const_cpow (x : ℂ)).comp (by fun_prop)
    have hkernel : Continuous (fun t : ℝ =>
        smoothAFEGaussianKernel ((c : ℂ) + (t : ℂ) * I)) := by
      unfold smoothAFEGaussianKernel
      exact (continuous_exp.comp (by fun_prop)).div
        (by fun_prop)
        (fun t hzero => by
          have hre : (((c : ℂ) + (t : ℂ) * I)).re = c := by simp
          rw [← hre] at hc
          exact (hc.ne' (congrArg Complex.re hzero)).elim)
    simpa [smoothAFEZetaMellinTerm, one_div] using
      (((hpowN.inv₀ (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hn))).mul hpowX).mul
        hkernel).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      simpa using norm_smoothAFEZetaMellinTerm_vertical_le hx hc n t

theorem summable_integral_norm_smoothAFEZetaMellinTerm
    {s : ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hsc : 1 < s.re + c) :
    Summable (fun n : ℕ => ∫ t : ℝ,
      ‖smoothAFEZetaMellinTerm s x n ((c : ℂ) + (t : ℂ) * I)‖) := by
  let D : ℝ := x ^ c * (Real.exp (c ^ 2) / c) *
    ∫ t : ℝ, Real.exp (-(t ^ 2))
  have hbase := summable_smoothAFEZetaMajorant hsc
  have hmajor : Summable (fun n : ℕ =>
      (1 / (n + 1 : ℝ) ^ (s.re + c)) * D) :=
    hbase.mul_right D
  refine Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) hmajor
  have hterm := smoothAFEZetaMellinTerm_verticalIntegrable
    (s := s) hx hc n
  have hgauss := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have hdom : Integrable (fun t : ℝ =>
      (((1 / (n + 1 : ℝ) ^ (s.re + c)) * x ^ c) *
        (Real.exp (c ^ 2) / c)) * Real.exp (-(t ^ 2))) := by
    simpa using hgauss.const_mul
      (((1 / (n + 1 : ℝ) ^ (s.re + c)) * x ^ c) *
        (Real.exp (c ^ 2) / c))
  calc
    ∫ t : ℝ, ‖smoothAFEZetaMellinTerm s x n ((c : ℂ) + (t : ℂ) * I)‖
      ≤ ∫ t : ℝ, (((1 / (n + 1 : ℝ) ^ (s.re + c)) * x ^ c) *
          (Real.exp (c ^ 2) / c)) * Real.exp (-(t ^ 2)) := by
        apply integral_mono_ae hterm.norm hdom
        exact Filter.Eventually.of_forall fun t =>
          norm_smoothAFEZetaMellinTerm_vertical_le hx hc n t
    _ = (1 / (n + 1 : ℝ) ^ (s.re + c)) * D := by
      rw [MeasureTheory.integral_const_mul]
      dsimp [D]
      ring

theorem integral_smoothAFEZetaMellinIntegrand_eq_tsum
    {s : ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hsc : 1 < s.re + c) :
    (∫ t : ℝ, smoothAFEZetaMellinIntegrand s x ((c : ℂ) + (t : ℂ) * I))
      = ∑' n : ℕ, ∫ t : ℝ,
          smoothAFEZetaMellinTerm s x n ((c : ℂ) + (t : ℂ) * I) := by
  calc
    (∫ t : ℝ, smoothAFEZetaMellinIntegrand s x ((c : ℂ) + (t : ℂ) * I))
      = ∫ t : ℝ, ∑' n : ℕ,
          smoothAFEZetaMellinTerm s x n ((c : ℂ) + (t : ℂ) * I) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t =>
          smoothAFEZetaMellinIntegrand_eq_tsum hsc
    _ = ∑' n : ℕ, ∫ t : ℝ,
          smoothAFEZetaMellinTerm s x n ((c : ℂ) + (t : ℂ) * I) := by
        symm
        apply MeasureTheory.integral_tsum_of_summable_integral_norm
        · exact fun n => smoothAFEZetaMellinTerm_verticalIntegrable hx hc n
        · exact summable_integral_norm_smoothAFEZetaMellinTerm hx hc hsc

end RHTower
