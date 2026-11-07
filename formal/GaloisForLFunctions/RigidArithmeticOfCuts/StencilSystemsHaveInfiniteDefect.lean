import GaloisForLFunctions.RHTower.ZetaStripBohrFourierCoefficients
import GaloisForLFunctions.RHTower.ZetaConvexityBound
import GaloisForLFunctions.RigidArithmeticOfCuts.ZerosOfADirichletPolynomialRecurEffectively
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Stencil systems have infinite defect

The Beurling space carries two distances from `ζ`. The count distance sees a stencil at bounded scale. The FE defect does
not. Let `G(s) = Σ_{n∈S} g(n) n^{-s}` be a Dirichlet polynomial; the system `ζ G` has count `a = 1 ∗ g`, read through floors.
Its defect on the critical line is

`D(t) = ζ(½ + it) (G(½ + it) − G(½ − it))`,

the function `g(t/2)` in the small-defect rigidity theorem `beurlingSystem_rigidity_of_small_critical_line_defect`.

**If `T⁻¹ ∫_0^T |D| → 0`, then `G` is constant.** In particular a nonconstant stencil has `∫ |D| = ∞`, at every height a
positive proportion of mass. Stencil systems lie at infinite FE distance from `ζ`, whatever their count distance.

The mechanism is the Bohr coefficient on the critical line: `T⁻¹ ∫_0^T ζ(½ + it) e^{iλt} dt` tends to `k^{-½}` at `λ = log k`
and to `0` off the logarithms of the integers. Against `m^{it}` the mean of `D` is `m^{-½} (a(m) − G(1))`. So a small defect
makes `a` constant, and Möbius inversion leaves `g = c δ₁`.
-/

open Complex Filter Topology MeasureTheory Set
open scoped Interval

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The integrand of the rectangle between the lines `½` and `¾`. -/
private def rectF (lam : ℝ) (s : ℂ) : ℂ := riemannZeta s * Complex.exp ((lam : ℂ) * (s - ((1 / 2 : ℝ) : ℂ)))

private lemma rectF_differentiableAt (lam : ℝ) {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ (rectF lam) s :=
  (differentiableAt_riemannZeta hs).mul (by fun_prop)

private lemma rectF_line (lam σ y : ℝ) :
    rectF lam (((σ : ℝ) : ℂ) + (y : ℂ) * I) = Complex.exp ((lam : ℂ) * ((σ - 1 / 2 : ℝ) : ℂ)) *
      (riemannZeta (((σ : ℝ) : ℂ) + (y : ℂ) * I) * Complex.exp ((lam : ℂ) * I * (y : ℂ))) := by
  rw [rectF, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The critical line reads the same Bohr coefficients.** The means of `ζ(½ + it) e^{iλt}` and `e^{λ/4} ζ(¾ + it) e^{iλt}` differ by
`o(1)`, by Cauchy on the rectangle and the convexity bound on its horizontal sides. -/
theorem tendsto_critical_average_sub (lam : ℝ) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * (∫ t in (0 : ℝ)..T,
        riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * Complex.exp ((lam : ℂ) * I * (t : ℂ))) -
      Complex.exp ((lam / 4 : ℝ) : ℂ) * ((T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
        riemannZeta (((3 / 4 : ℝ) : ℂ) + (t : ℂ) * I) * Complex.exp ((lam : ℂ) * I * (t : ℂ))))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hconv⟩ := _root_.RHTower.exists_norm_riemannZeta_le_convexity (η := 1 / 2) (by norm_num)
    (by norm_num)
  set E : ℝ := Real.exp (|lam| / 4) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- The bottom side.
  set B₀ : ℂ := ∫ x in (1 / 2 : ℝ)..(3 / 4 : ℝ), rectF lam ((x : ℂ) + ((0 : ℝ) : ℂ) * I) with hB₀
  -- The bound on the top side.
  have htop : ∀ T : ℝ, 8 ≤ T → ‖∫ x in (1 / 2 : ℝ)..(3 / 4 : ℝ), rectF lam ((x : ℂ) + (T : ℂ) * I)‖ ≤
      C * Real.sqrt T * E * |3 / 4 - 1 / 2| := by
    intro T hT
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le (by norm_num)] at hx
    obtain ⟨h1, h2⟩ := hx
    have hT0 : 0 < T := by linarith
    have hz := hconv x T (by linarith) (by linarith) hT
    have hexp : T ^ ((1 + 1 / 2 - x) / 2) ≤ Real.sqrt T := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hnorm : ‖Complex.exp ((lam : ℂ) * (((x : ℂ) + (T : ℂ) * I) - ((1 / 2 : ℝ) : ℂ)))‖ ≤ E := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      have hre : ((lam : ℂ) * (((x : ℂ) + (T : ℂ) * I) - ((1 / 2 : ℝ) : ℂ))).re = lam * (x - 1 / 2) := by
        simp
      rw [hre]
      have habs : |lam * (x - 1 / 2)| ≤ |lam| * (1 / 4) := by
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_le]
        constructor <;> linarith
      have := le_abs_self (lam * (x - 1 / 2))
      linarith
    rw [rectF, norm_mul]
    refine mul_le_mul (hz.trans (mul_le_mul_of_nonneg_left hexp hC.le)) hnorm (norm_nonneg _) ?_
    positivity
  -- The Cauchy identity.
  have hcauchy : ∀ T : ℝ, 8 ≤ T →
      (∫ t in (0 : ℝ)..T, riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          Complex.exp ((lam : ℂ) * I * (t : ℂ))) -
        Complex.exp ((lam / 4 : ℝ) : ℂ) * ∫ t in (0 : ℝ)..T,
          riemannZeta (((3 / 4 : ℝ) : ℂ) + (t : ℂ) * I) * Complex.exp ((lam : ℂ) * I * (t : ℂ)) =
      -I * (B₀ - ∫ x in (1 / 2 : ℝ)..(3 / 4 : ℝ), rectF lam ((x : ℂ) + (T : ℂ) * I)) := by
    intro T hT
    have hzre : (((1 / 2 : ℝ) : ℂ)).re = 1 / 2 := by simp
    have hzim : (((1 / 2 : ℝ) : ℂ)).im = 0 := by simp
    have hwre : (((3 / 4 : ℝ) : ℂ) + (T : ℂ) * I).re = 3 / 4 := by simp
    have hwim : (((3 / 4 : ℝ) : ℂ) + (T : ℂ) * I).im = T := by simp
    have hd : DifferentiableOn ℂ (rectF lam) ([[(((1 / 2 : ℝ) : ℂ)).re, (((3 / 4 : ℝ) : ℂ) + (T : ℂ) * I).re]] ×ℂ
        [[(((1 / 2 : ℝ) : ℂ)).im, (((3 / 4 : ℝ) : ℂ) + (T : ℂ) * I).im]]) := by
      intro s hs
      refine (rectF_differentiableAt lam ?_).differentiableWithinAt
      intro h1
      have hmem := (mem_reProdIm.mp hs).1
      rw [hzre, hwre, uIcc_of_le (by norm_num), h1] at hmem
      have h2 := hmem.2
      rw [Complex.one_re] at h2
      norm_num at h2
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (rectF lam) ((1 / 2 : ℝ) : ℂ)
      (((3 / 4 : ℝ) : ℂ) + (T : ℂ) * I) hd
    rw [hzre, hzim, hwre, hwim] at hrect
    have hline : ∀ σ : ℝ, (∫ y in (0 : ℝ)..T, rectF lam (((σ : ℝ) : ℂ) + (y : ℂ) * I)) =
        Complex.exp ((lam : ℂ) * ((σ - 1 / 2 : ℝ) : ℂ)) * ∫ y in (0 : ℝ)..T,
          riemannZeta (((σ : ℝ) : ℂ) + (y : ℂ) * I) * Complex.exp ((lam : ℂ) * I * (y : ℂ)) := by
      intro σ
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun y _ => rectF_line lam σ y
    rw [hline (3 / 4), hline (1 / 2)] at hrect
    have h1 : Complex.exp ((lam : ℂ) * ((1 / 2 - 1 / 2 : ℝ) : ℂ)) = 1 := by
      simp
    have h2 : Complex.exp ((lam : ℂ) * ((3 / 4 - 1 / 2 : ℝ) : ℂ)) = Complex.exp ((lam / 4 : ℝ) : ℂ) := by
      congr 1
      push_cast
      ring
    rw [h1, h2, one_mul] at hrect
    simp only [smul_eq_mul] at hrect
    rw [hB₀]
    have hI : I * I = -1 := Complex.I_mul_I
    linear_combination I * hrect + ((∫ t in (0 : ℝ)..T, riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          Complex.exp ((lam : ℂ) * I * (t : ℂ))) - Complex.exp ((lam / 4 : ℝ) : ℂ) * ∫ t in (0 : ℝ)..T,
          riemannZeta (((3 / 4 : ℝ) : ℂ) + (t : ℂ) * I) * Complex.exp ((lam : ℂ) * I * (t : ℂ))) * hI
  -- The limit.
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hroot : Tendsto (fun T : ℝ => (‖B₀‖ + C * Real.sqrt T * E * |3 / 4 - 1 / 2|) / T) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => ‖B₀‖ / T) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun T : ℝ => Real.sqrt T / T) atTop (𝓝 0) := by
      refine (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with T hT
      exact Real.sqrt_div_self.symm
    have h3 := h1.add (h2.const_mul (C * E * |3 / 4 - 1 / 2|))
    simp only [mul_zero, add_zero] at h3
    refine h3.congr fun T => ?_
    ring
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hroot
  filter_upwards [eventually_ge_atTop 8] with T hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  have hrew : (T : ℂ)⁻¹ * (∫ t in (0 : ℝ)..T, riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        Complex.exp ((lam : ℂ) * I * (t : ℂ))) -
      Complex.exp ((lam / 4 : ℝ) : ℂ) * ((T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
        riemannZeta (((3 / 4 : ℝ) : ℂ) + (t : ℂ) * I) * Complex.exp ((lam : ℂ) * I * (t : ℂ))) =
      (T : ℂ)⁻¹ * (-I * (B₀ - ∫ x in (1 / 2 : ℝ)..(3 / 4 : ℝ), rectF lam ((x : ℂ) + (T : ℂ) * I))) := by
    rw [← hcauchy T hT]
    ring
  rw [hrew, norm_mul, norm_mul, norm_inv, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg hT0.le, inv_mul_eq_div]
  refine div_le_div_of_nonneg_right ((norm_sub_le _ _).trans ?_) hT0.le
  linarith [htop T hT]

/-- **The Bohr coefficient on the critical line at `log n`.** -/
theorem tendsto_critical_average_log {n₀ : ℕ} (hn₀ : 1 ≤ n₀) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
        riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          Complex.exp ((Real.log (n₀ : ℝ) : ℂ) * I * (t : ℂ)))
      atTop (𝓝 (((n₀ : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
  have hn0 : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  have h1 := _root_.RHTower.tendsto_zeta_line_mul_char_average_log (σ := 3 / 4) (by norm_num) (by norm_num) hn₀
  have h2 := (h1.const_mul (Complex.exp ((Real.log (n₀ : ℝ) / 4 : ℝ) : ℂ))).add
    (tendsto_critical_average_sub (Real.log (n₀ : ℝ)))
  have hval : Complex.exp ((Real.log (n₀ : ℝ) / 4 : ℝ) : ℂ) * (((n₀ : ℝ) ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) + 0 =
      (((n₀ : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [add_zero, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    congr 1
    rw [Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0, ← Real.exp_add]
    congr 1
    ring
  rw [hval] at h2
  refine h2.congr fun T => ?_
  ring

/-- **The Bohr coefficient on the critical line off the spectrum.** -/
theorem tendsto_critical_average_of_forall_ne {lam : ℝ} (hlam : ∀ n : ℕ, 1 ≤ n → lam ≠ Real.log (n : ℝ)) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
        riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * Complex.exp ((lam : ℂ) * I * (t : ℂ)))
      atTop (𝓝 0) := by
  have h1 := _root_.RHTower.tendsto_zeta_line_mul_char_average_of_forall_ne (σ := 3 / 4) (by norm_num)
    (by norm_num) hlam
  have h2 := (h1.const_mul (Complex.exp ((lam / 4 : ℝ) : ℂ))).add (tendsto_critical_average_sub lam)
  simp only [mul_zero, add_zero] at h2
  refine h2.congr fun T => ?_
  ring

/-! ### The mean of the defect -/

/-- The critical line, in the variable `t`. -/
private lemma line_ne_one (t : ℝ) : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := by
  intro h
  have h1 := congrArg Complex.re h
  simp at h1

theorem continuous_zeta_line : Continuous fun t : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hf : ContinuousAt (fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) t := by fun_prop
  exact ContinuousAt.comp (f := fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
    (differentiableAt_riemannZeta (line_ne_one t)).continuousAt hf

/-- The Bohr mean of `ζ` at frequency `λ`. -/
def bohrMean (lam T : ℝ) : ℂ := (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
  riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * Complex.exp ((lam : ℂ) * I * (t : ℂ))

/-- The frequency `log m − log n`: the coefficient is `(m/n)^{-½}` when `n ∣ m`, and vanishes otherwise, because
`m/n` is then not an integer. -/
theorem tendsto_bohrMean_sub {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Tendsto (bohrMean (Real.log m - Real.log n)) atTop
      (𝓝 (if n ∣ m then (((n : ℝ) ^ ((1 / 2 : ℝ)) * (m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  split_ifs with hdvd
  · obtain ⟨k, rfl⟩ := hdvd
    have hk : 1 ≤ k := Nat.pos_of_mul_pos_left (by omega : 0 < n * k)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hlog : Real.log ((n * k : ℕ) : ℝ) - Real.log n = Real.log k := by
      push_cast
      rw [Real.log_mul hn0.ne' hk0.ne']
      ring
    rw [hlog]
    have hval : (n : ℝ) ^ ((1 / 2 : ℝ)) * ((n * k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
      push_cast
      rw [Real.mul_rpow hn0.le hk0.le, ← mul_assoc, ← Real.rpow_add hn0]
      norm_num
    rw [hval]
    exact tendsto_critical_average_log hk
  · refine tendsto_critical_average_of_forall_ne fun k hk h => hdvd ?_
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have heq : Real.log m = Real.log ((n : ℝ) * k) := by
      rw [Real.log_mul hn0.ne' hk0.ne']
      linarith
    have hval := Real.log_injOn_pos (Set.mem_Ioi.mpr hm0) (Set.mem_Ioi.mpr (mul_pos hn0 hk0)) heq
    exact ⟨k, by exact_mod_cast hval⟩

/-- The frequency `log m + log n` is the logarithm of `m n`. -/
theorem tendsto_bohrMean_add {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Tendsto (bohrMean (Real.log m + Real.log n)) atTop
      (𝓝 ((((m : ℝ) * n) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := tendsto_critical_average_log (n₀ := m * n) (Nat.mul_pos hm hn)
  have hcast : ((m * n : ℕ) : ℝ) = (m : ℝ) * n := by push_cast; ring
  rw [hcast, Real.log_mul hm0.ne' hn0.ne'] at h
  exact h

/-- The FE defect of the stencil system `ζ G` on the critical line. -/
def stencilDefect (S : Finset ℕ) (g : ℕ → ℂ) (t : ℝ) : ℂ :=
  riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
    (dirichletPolyOf S g (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) - dirichletPolyOf S g (((1 / 2 : ℝ) : ℂ) - (t : ℂ) * I))

/-- The count of the stencil system at `m`: the convolution `1 ∗ g`. -/
def stencilCount (S : Finset ℕ) (g : ℕ → ℂ) (m : ℕ) : ℂ := ∑ n ∈ S, if n ∣ m then g n else 0

/-- `G(1)`, the slope of the count. -/
def polySlope (S : Finset ℕ) (g : ℕ → ℂ) : ℂ := ∑ n ∈ S, g n / n

/-- `n^{-(½ + it)}` as an amplitude times a phase. -/
private lemma cpow_line {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    ((n : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
      (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(Real.log n : ℂ) * I * (t : ℂ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hn0.le, Real.rpow_def_of_pos hn0, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `n^{-(½ − it)}` as an amplitude times a phase. -/
private lemma cpow_line_conj {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    ((n : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) - (t : ℂ) * I)) =
      (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp ((Real.log n : ℂ) * I * (t : ℂ)) := by
  have h := cpow_line hn (-t)
  have h1 : ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I = ((1 / 2 : ℝ) : ℂ) - (t : ℂ) * I := by
    push_cast
    ring
  rw [h1] at h
  rw [h]
  congr 2
  push_cast
  ring

/-- The defect against a character is a finite sum of Bohr integrands. -/
private lemma stencilDefect_mul_char {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (g : ℕ → ℂ) (m : ℕ) (t : ℝ) :
    stencilDefect S g t * Complex.exp ((Real.log m : ℂ) * I * (t : ℂ)) =
      ∑ n ∈ S, g n * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * I * (t : ℂ)) -
          riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            Complex.exp (((Real.log m + Real.log n : ℝ) : ℂ) * I * (t : ℂ))) := by
  rw [stencilDefect, dirichletPolyOf, dirichletPolyOf, ← Finset.sum_sub_distrib, mul_assoc, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [cpow_line (hS n hn), cpow_line_conj (hS n hn)]
  have h1 : Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * I * (t : ℂ)) =
      Complex.exp (-(Real.log n : ℂ) * I * (t : ℂ)) * Complex.exp ((Real.log m : ℂ) * I * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (((Real.log m + Real.log n : ℝ) : ℂ) * I * (t : ℂ)) =
      Complex.exp ((Real.log n : ℂ) * I * (t : ℂ)) * Complex.exp ((Real.log m : ℂ) * I * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, h2]
  ring

private lemma continuous_zetaChar (lam : ℝ) : Continuous fun t : ℝ =>
    riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * Complex.exp ((lam : ℂ) * I * (t : ℂ)) :=
  continuous_zeta_line.mul (by fun_prop)

/-- **The mean of the defect.** Against `m^{it}`, the defect of a stencil system has mean `m^{-½} (a(m) − G(1))`. -/
theorem tendsto_stencilDefect_average {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (g : ℕ → ℂ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
        stencilDefect S g t * Complex.exp ((Real.log m : ℂ) * I * (t : ℂ))) atTop
      (𝓝 ((((m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (stencilCount S g m - polySlope S g))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hexpand : ∀ T : ℝ, (T : ℂ)⁻¹ * (∫ t in (0 : ℝ)..T,
      stencilDefect S g t * Complex.exp ((Real.log m : ℂ) * I * (t : ℂ))) =
      ∑ n ∈ S, g n * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (bohrMean (Real.log m - Real.log n) T - bohrMean (Real.log m + Real.log n) T) := by
    intro T
    simp_rw [stencilDefect_mul_char hS g m]
    have hint : ∀ n ∈ S, IntervalIntegrable (fun t : ℝ => g n * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * I * (t : ℂ)) -
          riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            Complex.exp (((Real.log m + Real.log n : ℝ) : ℂ) * I * (t : ℂ)))) volume 0 T := fun n _ =>
      (((continuous_zetaChar (Real.log m - Real.log n)).sub
        (continuous_zetaChar (Real.log m + Real.log n))).const_mul _).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum hint, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      ((continuous_zetaChar _).intervalIntegrable _ _) ((continuous_zetaChar _).intervalIntegrable _ _), bohrMean,
      bohrMean]
    ring
  simp_rw [hexpand]
  have hlim : Tendsto (fun T : ℝ => ∑ n ∈ S, g n * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (bohrMean (Real.log m - Real.log n) T - bohrMean (Real.log m + Real.log n) T)) atTop
      (𝓝 (∑ n ∈ S, g n * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((if n ∣ m then (((n : ℝ) ^ ((1 / 2 : ℝ)) * (m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0) -
          (((m : ℝ) * n) ^ (-(1 / 2 : ℝ)) : ℝ)))) :=
    tendsto_finsetSum _ fun n hn => ((tendsto_bohrMean_sub hm (hS n hn)).sub
      (tendsto_bohrMean_add hm (hS n hn))).const_mul _
  convert hlim using 2
  rw [stencilCount, polySlope, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 := hS n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hhalf : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ ((1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hn0]
    norm_num
  have hab : (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((n : ℝ) ^ ((1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hhalf, Complex.ofReal_one]
  have hprod : (((m : ℝ) * n) ^ (-(1 / 2 : ℝ))) = (m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.mul_rpow hm0.le hn0.le
  have hsq : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) = (n : ℝ)⁻¹ := by
    rw [← Real.rpow_add hn0, ← Real.rpow_neg_one]
    norm_num
  have haa : (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = (n : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, hsq, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [hprod]
  by_cases hd : n ∣ m
  · simp only [if_pos hd, Complex.ofReal_mul]
    rw [div_eq_mul_inv (g n) (n : ℂ), ← haa]
    linear_combination (-(g n * (((m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) * hab
  · simp only [if_neg hd, Complex.ofReal_mul]
    rw [div_eq_mul_inv (g n) (n : ℂ), ← haa]
    ring

/-- A constant count forces a constant stencil, by Möbius inversion in its elementary form. -/
theorem eq_zero_of_stencilCount_const {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) {g : ℕ → ℂ} {c : ℂ}
    (hc : ∀ m, 1 ≤ m → stencilCount S g m = c) : ∀ n ∈ S, n ≠ 1 → g n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hn1
    have hn2 : 1 ≤ n := hS n hn
    have hdiff : stencilCount S g n - stencilCount S g 1 = 0 := by
      rw [hc n hn2, hc 1 le_rfl, sub_self]
    rw [stencilCount, stencilCount, ← Finset.sum_sub_distrib] at hdiff
    rw [Finset.sum_eq_single_of_mem n hn ?_] at hdiff
    · have hnd : ¬ n ∣ 1 := fun h => hn1 (Nat.dvd_one.mp h)
      simpa [hnd] using hdiff
    · intro d hd hdn
      by_cases hd1 : d = 1
      · simp [hd1]
      · have hd1' : ¬ d ∣ 1 := fun h => hd1 (Nat.dvd_one.mp h)
        by_cases hdvd : d ∣ n
        · have hlt : d < n := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd) hdn
          simp [hdvd, hd1', ih d hlt hd hd1]
        · simp [hdvd, hd1']

/-- **A sublinear defect forces a constant stencil.** A stencil system with `T⁻¹ ∫_0^T |D| → 0` has `G` constant. -/
theorem eq_zero_of_defect_sublinear {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) {g : ℕ → ℂ}
    (hD : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖stencilDefect S g t‖) atTop (𝓝 0)) :
    ∀ n ∈ S, n ≠ 1 → g n = 0 := by
  refine eq_zero_of_stencilCount_const hS (c := polySlope S g) fun m hm => ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlim := tendsto_stencilDefect_average hS g hm
  have hzero : Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
      stencilDefect S g t * Complex.exp ((Real.log m : ℂ) * I * (t : ℂ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hD
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hT.le]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hT.le)
    refine (intervalIntegral.norm_integral_le_integral_norm hT.le).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [norm_mul]
    have hnorm : ‖Complex.exp ((Real.log m : ℂ) * I * (t : ℂ))‖ = 1 := by
      have h : (Real.log m : ℂ) * I * (t : ℂ) = ((Real.log m * t : ℝ) : ℂ) * I := by
        push_cast
        ring
      rw [h, Complex.norm_exp_ofReal_mul_I]
    rw [hnorm, mul_one]
  have hval := tendsto_nhds_unique hlim hzero
  have hne : (((m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hm0 _).ne'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hval).resolve_left hne)

/-- **Stencil systems have infinite defect.** An integrable defect forces `G` to be constant. -/
theorem eq_zero_of_integrable_stencilDefect {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) {g : ℕ → ℂ}
    (hint : IntegrableOn (stencilDefect S g) (Ioi 0)) : ∀ n ∈ S, n ≠ 1 → g n = 0 := by
  refine eq_zero_of_defect_sublinear hS ?_
  have hM : Tendsto (fun T : ℝ => (∫ t in Ioi (0 : ℝ), ‖stencilDefect S g t‖) / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' ?_ ?_ hM
  · filter_upwards [eventually_gt_atTop 0] with T hT
    exact mul_nonneg (inv_nonneg.mpr hT.le) (intervalIntegral.integral_nonneg hT.le fun _ _ => norm_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with T hT
    rw [inv_mul_eq_div]
    refine div_le_div_of_nonneg_right ?_ hT.le
    rw [intervalIntegral.integral_of_le hT.le]
    exact setIntegral_mono_set hint.norm (Eventually.of_forall fun _ => norm_nonneg _)
      (Ioc_subset_Ioi_self.eventuallyLE)

end GaloisForLFunctions.RigidArithmeticOfCuts
