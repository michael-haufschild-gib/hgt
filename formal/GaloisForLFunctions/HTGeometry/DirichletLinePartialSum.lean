import Mathlib

/-!
# Bounded Dirichlet partial sums on the one-line and log-Cesàro equidistribution

The critical weak-Schatten residue of a quasi-inner Hankel defect is evaluated (Connes–Consani,
Gauss-component hierarchy) through a **harmonic logarithmic rotation**: for every continuous
one-periodic `f`,
`(1/log N) ∑_{n ≤ N} f(δ_n)/n → ∫₀¹ f`, where `δ_n = log(n/L)/(mL) mod 1`.
By trigonometric approximation this reduces to a single arithmetic fact — the boundedness of the
Dirichlet partial sums on the abscissa `Re s = 1`:
`∑_{n ≤ N} n^{-1+iα}` stays uniformly bounded for every real `α ≠ 0`, hence its log-Cesàro mean
vanishes.

The bound is the Euler–Maclaurin comparison of the sum with its integral: writing
`g(x) = x^{-1+iα}` with antiderivative `G(x) = x^{iα}/(iα)` (`‖G‖ ≡ 1/|α|`), the telescoped integral
part `∑ (G(n+1) − G(n)) = G(N+1) − G(1)` is bounded by `2/|α|`, and each correction
`g(n) − ∫_n^{n+1} g` is controlled by the mean-value estimate `‖g(n) − g(x)‖ ≤ ‖-1+iα‖/n²`, summed
against `∑ 1/n²`.  The result is the uniform bound `‖∑_{n≤N} g(n)‖ ≤ 2/|α| + ‖-1+iα‖·∑ 1/n²`.

* `gpow`, `Gpow` — the one-line power `x^{-1+iα}` and its antiderivative.
* `dirichlet_line_partialSum_bounded` — the uniform partial-sum bound.
* `dirichlet_line_logCesaro` — the log-Cesàro mean of a nonzero one-line mode tends to `0`.
-/

open Complex MeasureTheory Finset

namespace GaloisForLFunctions

noncomputable def gpow (α : ℝ) (x : ℝ) : ℂ := Complex.exp ((-1 + α * Complex.I) * (Real.log x : ℂ))
noncomputable def Gpow (α : ℝ) (x : ℝ) : ℂ := Complex.exp ((α * Complex.I) * (Real.log x : ℂ)) / (α * Complex.I)

theorem hasDerivAt_gpow (α : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gpow α) (gpow α x * (-1 + α * Complex.I) / x) x := by
  have hlog := (Real.hasDerivAt_log hx.ne').ofReal_comp
  have hg := (hlog.const_mul (-1 + α * Complex.I)).cexp
  convert hg using 1
  rw [gpow, Complex.ofReal_inv]; ring

theorem hasDerivAt_Gpow (α : ℝ) (hα : α ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (Gpow α) (gpow α x) x := by
  have hw : (α : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hα) Complex.I_ne_zero
  have hlog := (Real.hasDerivAt_log hx.ne').ofReal_comp
  have hG := ((hlog.const_mul (α * Complex.I)).cexp).div_const (α * Complex.I)
  convert hG using 1
  have hxc : (↑x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hexp : Complex.exp (-(↑(Real.log x) : ℂ)) = (↑x : ℂ)⁻¹ := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hx]
  rw [gpow]
  have hsplit : (-1 + (α:ℂ) * Complex.I) * ↑(Real.log x)
      = (α:ℂ) * Complex.I * ↑(Real.log x) + (-(↑(Real.log x))) := by ring
  rw [hsplit, Complex.exp_add, hexp, Complex.ofReal_inv, mul_div_assoc]
  congr 1
  rw [mul_comm ((α:ℂ) * Complex.I) ((↑x:ℂ)⁻¹), mul_div_assoc, div_self hw, mul_one]

theorem continuousOn_gpow (α : ℝ) : ContinuousOn (gpow α) (Set.Ioi (0:ℝ)) := by
  have hlog : ContinuousOn (fun x : ℝ => (Real.log x : ℂ)) (Set.Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hx))
  exact (hlog.const_mul (-1 + α * Complex.I)).cexp

theorem norm_gpow (α : ℝ) {x : ℝ} (hx : 0 < x) : ‖gpow α x‖ = x⁻¹ := by
  rw [gpow, Complex.norm_exp]
  have hre : ((-1 + (α:ℂ) * Complex.I) * (Real.log x : ℂ)).re = -Real.log x := by
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  rw [hre, Real.exp_neg, Real.exp_log hx]

theorem norm_Gpow (α : ℝ) (_hα : α ≠ 0) {x : ℝ} (_hx : 0 < x) : ‖Gpow α x‖ = |α|⁻¹ := by
  rw [Gpow, norm_div, Complex.norm_exp]
  have hre : (((α:ℂ) * Complex.I) * (Real.log x : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    one_div]

theorem intervalIntegrable_gpow (α : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (gpow α) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_gpow α).mono
  rw [Set.uIcc_of_le hab]; exact fun x hx => lt_of_lt_of_le ha hx.1

theorem integral_gpow (α : ℝ) (hα : α ≠ 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, gpow α x = Gpow α b - Gpow α a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hasDerivAt_Gpow α hα (lt_of_lt_of_le ha hx.1)
  · exact intervalIntegrable_gpow α ha hab

theorem gpow_diff_le (α : ℝ) {k x : ℝ} (hk : 1 ≤ k) (hx : x ∈ Set.Icc k (k+1)) :
    ‖gpow α k - gpow α x‖ ≤ ‖(-1 + α * Complex.I)‖ / k ^ 2 := by
  have hk0 : (0:ℝ) < k := by linarith
  set C := ‖(-1 + α * Complex.I)‖ / k ^ 2 with hC
  have hconv : Convex ℝ (Set.Icc k (k+1)) := convex_Icc _ _
  have hderiv : ∀ y ∈ Set.Icc k (k+1), HasDerivWithinAt (gpow α)
      (gpow α y * (-1 + α * Complex.I) / y) (Set.Icc k (k+1)) y := by
    intro y hy
    exact (hasDerivAt_gpow α (by simp only [Set.mem_Icc] at hy; linarith [hy.1])).hasDerivWithinAt
  have hbound : ∀ y ∈ Set.Icc k (k+1), ‖gpow α y * (-1 + α * Complex.I) / y‖ ≤ C := by
    intro y hy
    simp only [Set.mem_Icc] at hy
    have hy0 : (0:ℝ) < y := by linarith [hy.1]
    rw [norm_div, norm_mul, norm_gpow α hy0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0, hC,
      show y⁻¹ * ‖(-1 + α * Complex.I)‖ / y = ‖(-1 + α * Complex.I)‖ / y^2 from by field_simp]
    gcongr
    nlinarith [hy.1, hk0]
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hconv
    (Set.left_mem_Icc.mpr (by linarith : k ≤ k+1)) hx
  rw [norm_sub_rev]
  refine le_trans hmvt ?_
  have hxk : ‖x - k‖ ≤ 1 := by
    simp only [Set.mem_Icc] at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2]
  calc C * ‖x - k‖ ≤ C * 1 := by apply mul_le_mul_of_nonneg_left hxk; rw [hC]; positivity
    _ = C := mul_one C

theorem corr_bound (α : ℝ) (_hα : α ≠ 0) {k : ℝ} (hk : 1 ≤ k) :
    ‖gpow α k - ∫ x in k..(k+1), gpow α x‖ ≤ ‖(-1 + α * Complex.I)‖ / k ^ 2 := by
  have hk0 : (0:ℝ) < k := by linarith
  have hkk1 : k ≤ k + 1 := by linarith
  have hII : IntervalIntegrable (gpow α) volume k (k+1) := intervalIntegrable_gpow α hk0 hkk1
  have hconst : ∫ _x in k..(k+1), gpow α k = gpow α k := by
    rw [intervalIntegral.integral_const]; simp
  have hnormII : IntervalIntegrable (fun x => ‖gpow α k - gpow α x‖) volume k (k+1) := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_const.sub ((continuousOn_gpow α).mono ?_)).norm
    rw [Set.uIcc_of_le hkk1]; exact fun x hx => lt_of_lt_of_le hk0 hx.1
  have hsub : gpow α k - ∫ x in k..(k+1), gpow α x = ∫ x in k..(k+1), (gpow α k - gpow α x) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_const) hII, hconst]
  rw [hsub]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hkk1) ?_
  calc ∫ x in k..(k+1), ‖gpow α k - gpow α x‖
      ≤ ∫ _x in k..(k+1), (‖(-1 + α * Complex.I)‖ / k ^ 2) := by
        apply intervalIntegral.integral_mono_on hkk1 hnormII intervalIntegrable_const
        intro x hx; exact gpow_diff_le α hk hx
    _ = ‖(-1 + α * Complex.I)‖ / k ^ 2 := by rw [intervalIntegral.integral_const]; simp

theorem dirichlet_line_partialSum_bounded (α : ℝ) (hα : α ≠ 0) :
    ∃ C : ℝ, ∀ N : ℕ, ‖∑ n ∈ Finset.range N, gpow α ((n:ℝ) + 1)‖ ≤ C := by
  set s := ‖(-1 + α * Complex.I)‖ with hsdef
  have h2 : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hb : Summable (fun k : ℕ => (1:ℝ)/((k:ℝ)+1)^2) := by
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h2
  have hshift : Summable (fun k : ℕ => s / ((k:ℝ)+1)^2) := by
    have hh := hb.mul_left s
    simp only [mul_one_div] at hh
    exact hh
  refine ⟨2 * |α|⁻¹ + ∑' k : ℕ, s / ((k:ℝ)+1)^2, fun N => ?_⟩
  have hdecomp : ∀ n : ℕ, gpow α ((n:ℝ)+1)
      = (Gpow α ((n:ℝ)+1+1) - Gpow α ((n:ℝ)+1))
        + (gpow α ((n:ℝ)+1) - (Gpow α ((n:ℝ)+1+1) - Gpow α ((n:ℝ)+1))) := fun n => by ring
  rw [Finset.sum_congr rfl (fun n _ => hdecomp n), Finset.sum_add_distrib]
  have htele : ∑ n ∈ Finset.range N, (Gpow α ((n:ℝ)+1+1) - Gpow α ((n:ℝ)+1))
      = Gpow α ((N:ℝ)+1) - Gpow α 1 := by
    have hsr := Finset.sum_range_sub (fun n : ℕ => Gpow α ((n:ℝ)+1)) N
    calc ∑ n ∈ Finset.range N, (Gpow α ((n:ℝ)+1+1) - Gpow α ((n:ℝ)+1))
        = ∑ n ∈ Finset.range N, (Gpow α (((n+1:ℕ):ℝ)+1) - Gpow α ((n:ℝ)+1)) := by
          apply Finset.sum_congr rfl; intro i _; push_cast; ring_nf
      _ = Gpow α ((N:ℝ)+1) - Gpow α 1 := by simpa using hsr
  rw [htele]
  refine le_trans (norm_add_le _ _) ?_
  have hG1 : ‖Gpow α ((N:ℝ)+1) - Gpow α 1‖ ≤ 2 * |α|⁻¹ := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_Gpow α hα (by positivity : (0:ℝ) < (N:ℝ)+1), norm_Gpow α hα (by norm_num : (0:ℝ)<1)]
    linarith
  have hcorr : ‖∑ n ∈ Finset.range N,
        (gpow α ((n:ℝ)+1) - (Gpow α ((n:ℝ)+1+1) - Gpow α ((n:ℝ)+1)))‖
      ≤ ∑' k : ℕ, s / ((k:ℝ)+1)^2 := by
    refine le_trans (norm_sum_le _ _) ?_
    have hstep : ∑ n ∈ Finset.range N,
          ‖gpow α ((n:ℝ)+1) - (Gpow α ((n:ℝ)+1+1) - Gpow α ((n:ℝ)+1))‖
        ≤ ∑ n ∈ Finset.range N, s / ((n:ℝ)+1)^2 := by
      apply Finset.sum_le_sum
      intro n _
      have hk : (1:ℝ) ≤ (n:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
      have hcb := corr_bound α hα hk
      rw [integral_gpow α hα (by positivity : (0:ℝ) < (n:ℝ)+1) (by linarith)] at hcb
      exact hcb
    exact le_trans hstep
      (Summable.sum_le_tsum (Finset.range N) (fun k _ => by positivity) hshift)
  linarith [hG1, hcorr]


theorem dirichlet_line_logCesaro (α : ℝ) (hα : α ≠ 0) :
    Filter.Tendsto (fun N : ℕ => ‖∑ n ∈ Finset.range N, gpow α ((n:ℝ)+1)‖ / Real.log N)
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := dirichlet_line_partialSum_bounded α hα
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hub : Filter.Tendsto (fun N : ℕ => C / Real.log N) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply squeeze_zero' (g := fun N : ℕ => C / Real.log N) ?_ ?_ hub
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact div_nonneg (norm_nonneg _) (Real.log_nonneg (by exact_mod_cast hN))
  · filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hC N) (inv_nonneg.mpr hlogpos.le)

end GaloisForLFunctions
