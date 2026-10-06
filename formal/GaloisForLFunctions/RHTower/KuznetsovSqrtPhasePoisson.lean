import GaloisForLFunctions.RHTower.KuznetsovQuadraticPhase
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries

/-!
# Poisson summation for `Σ_n η(√(n/N)) e(zn + B√n)`

Let `η` be a fixed smooth cutoff, `η = 1` on `[1, 3/2]`, supported in `(19/20, 31/20)`, and
`f(t) = η(√(t/N)) e(zt + B√t)`.  The substitution `t = Nσ²` gives

`f̂(u) = N ∫ 2σ η(σ) e((z − u)Nσ² + B√N σ) dσ`  (`fourier_sqrtSumFun`),

a quadratic phase `Ξ(σ² − τσ)` with `Ξ = (z − u)N`, `τ = −B√N/Ξ`, so non-stationary phase gives
`|f̂(u)| ≤ C_p N |(z − u)N|^{−p}` as long as `|B|√N ≤ (5/3)|z − u|N`.  For `z = h/c` with `0 ≤ h < c`
and `|B| c ≤ (5/3)√N`, Poisson summation gives

`|Σ_n f(n) − [h = 0] f̂_{0}(0)| ≤ C_p N (c/N)^p`  (`exists_tsum_sqrtSumFun_sub_le`),

and the diagonal term satisfies `|f̂_0(0)| ≤ 3N` and `|f̂_0(0)| ≤ D √N/|B|` (`norm_sqrtDiag_le`,
`exists_sqrtDiag_le`).
-/

open MeasureTheory Set Filter Complex Asymptotics
open scoped FourierTransform

namespace GaloisForLFunctions.RHTower.KuznetsovSeparation

noncomputable section

/-! ## The cutoff and the amplitude -/

/-- The cutoff `η`: `1` on `[1, 3/2]`, supported in `(19/20, 31/20)`. -/
def sqrtBump : ContDiffBump (5 / 4 : ℝ) := ⟨1 / 4, 3 / 10, by norm_num, by norm_num⟩

/-- The cutoff as a function. -/
def sqrtWeight (σ : ℝ) : ℝ := sqrtBump σ

theorem sqrtWeight_eq_one {σ : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 3 / 2) : sqrtWeight σ = 1 := by
  refine sqrtBump.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  change -(1 / 4) ≤ σ - 5 / 4 ∧ σ - 5 / 4 ≤ 1 / 4
  constructor <;> linarith

theorem sqrtWeight_eq_zero {σ : ℝ} (h : σ ≤ 19 / 20 ∨ 31 / 20 ≤ σ) : sqrtWeight σ = 0 := by
  refine sqrtBump.zero_of_le_dist ?_
  rw [Real.dist_eq]
  change 3 / 10 ≤ |σ - 5 / 4|
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem sqrtWeight_nonneg (σ : ℝ) : 0 ≤ sqrtWeight σ := sqrtBump.nonneg
theorem sqrtWeight_le_one (σ : ℝ) : sqrtWeight σ ≤ 1 := sqrtBump.le_one
theorem contDiff_sqrtWeight : ContDiff ℝ (⊤ : ℕ∞) sqrtWeight := sqrtBump.contDiff
theorem continuous_sqrtWeight : Continuous sqrtWeight := sqrtBump.continuous

/-- The amplitude `2σ η(σ)` after the substitution `t = Nσ²`. -/
def sqrtAmp (σ : ℝ) : ℂ := ((2 * σ * sqrtWeight σ : ℝ) : ℂ)

theorem contDiff_sqrtAmp : ContDiff ℝ (⊤ : ℕ∞) sqrtAmp :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).mul contDiff_sqrtWeight)

theorem sqrtAmp_eventually_zero {σ : ℝ} (h : σ < 19 / 20 ∨ 31 / 20 < σ) :
    sqrtAmp =ᶠ[nhds σ] fun _ => 0 := by
  rcases h with h | h
  · filter_upwards [Iio_mem_nhds h] with y hy
    simp [sqrtAmp, sqrtWeight_eq_zero (Or.inl hy.le)]
  · filter_upwards [Ioi_mem_nhds h] with y hy
    simp [sqrtAmp, sqrtWeight_eq_zero (Or.inr hy.le)]

theorem iteratedDeriv_sqrtAmp_eq_zero {σ : ℝ} (h : σ < 19 / 20 ∨ 31 / 20 < σ) (i : ℕ) :
    iteratedDeriv i sqrtAmp σ = 0 := by
  rw [(sqrtAmp_eventually_zero h).iteratedDeriv_eq]
  cases i <;> simp

theorem norm_sqrtAmp_le {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 8 / 5) : ‖sqrtAmp σ‖ ≤ 16 / 5 := by
  rw [sqrtAmp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (by have := sqrtWeight_nonneg σ; positivity)]
  have := sqrtWeight_le_one σ
  have := sqrtWeight_nonneg σ
  nlinarith

/-! ## The summand and its Fourier transform -/

/-- `f(t) = η(√(t/N)) e(zt + B√t)`. -/
def sqrtSumFun (N z B t : ℝ) : ℂ :=
  (sqrtWeight (Real.sqrt (t / N)) : ℂ) *
    cexp (((2 * Real.pi * (z * t + B * Real.sqrt t)) : ℝ) * I)

theorem continuous_sqrtSumFun (N z B : ℝ) : Continuous (sqrtSumFun N z B) := by
  unfold sqrtSumFun
  have h1 : Continuous fun t : ℝ => sqrtWeight (Real.sqrt (t / N)) :=
    continuous_sqrtWeight.comp (Real.continuous_sqrt.comp (continuous_id.div_const N))
  have h2 : Continuous fun t : ℝ => 2 * Real.pi * (z * t + B * Real.sqrt t) := by
    have := Real.continuous_sqrt; fun_prop
  exact (continuous_ofReal.comp h1).mul ((continuous_ofReal.comp h2).mul continuous_const).cexp

theorem sqrtSumFun_eq_zero {N z B t : ℝ} (hN : 0 < N)
    (ht : t < (19 / 20) ^ 2 * N ∨ (31 / 20) ^ 2 * N < t) : sqrtSumFun N z B t = 0 := by
  rw [sqrtSumFun, sqrtWeight_eq_zero, Complex.ofReal_zero, zero_mul]
  rcases ht with ht | ht
  · left
    have : t / N ≤ (19 / 20) ^ 2 := by rw [div_le_iff₀ hN]; linarith
    calc Real.sqrt (t / N) ≤ Real.sqrt ((19 / 20) ^ 2) := Real.sqrt_le_sqrt this
      _ = 19 / 20 := Real.sqrt_sq (by norm_num)
  · right
    have : (31 / 20) ^ 2 < t / N := by rw [lt_div_iff₀ hN]; linarith
    exact ((Real.lt_sqrt (by norm_num)).2 this).le

/-- `f̂(u) = N ∫ 2σ η(σ) e((z − u)Nσ² + B√N σ) dσ`. -/
theorem fourier_sqrtSumFun {N : ℝ} (hN : 0 < N) (z B u : ℝ) :
    𝓕 (sqrtSumFun N z B) u = (N : ℂ) * ∫ σ in (9 / 10 : ℝ)..(8 / 5), sqrtAmp σ *
      cexp (((2 * Real.pi * ((z - u) * N * σ ^ 2 + B * Real.sqrt N * σ)) : ℝ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  set g : ℝ → ℂ := fun t => cexp (((-2 * Real.pi * t * u : ℝ)) * I) • sqrtSumFun N z B t
  have hg : Continuous g := by
    have := continuous_sqrtSumFun N z B
    simp only [g, smul_eq_mul]; fun_prop
  have hsupp : ∀ t ∉ Icc (N * (9 / 10) ^ 2) (N * (8 / 5) ^ 2), g t = 0 := fun t ht => by
    simp only [g]
    rw [sqrtSumFun_eq_zero hN, smul_zero]
    rcases not_and_or.1 ht with h | h
    · left; push Not at h; nlinarith
    · right; push Not at h; nlinarith
  have hle : N * (9 / 10) ^ 2 ≤ N * (8 / 5) ^ 2 := by nlinarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  have hsub := intervalIntegral.integral_deriv_smul_comp (a := 9 / 10) (b := 8 / 5)
    (f := fun σ => N * σ ^ 2) (f' := fun σ => 2 * N * σ) (g := g)
    (fun σ _ => by
      have := ((hasDerivAt_pow 2 σ).const_mul N)
      refine this.congr_deriv ?_; simp; ring)
    (by fun_prop) hg
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [uIcc_of_le (by norm_num)] at hσ
  have hσ0 : 0 ≤ σ := by linarith [hσ.1]
  have h1 : Real.sqrt (N * σ ^ 2 / N) = σ := by
    rw [show N * σ ^ 2 / N = σ ^ 2 by field_simp, Real.sqrt_sq hσ0]
  have h1' : N * σ ^ 2 / N = σ ^ 2 := by field_simp
  have h2 : Real.sqrt (N * σ ^ 2) = Real.sqrt N * σ := by
    rw [Real.sqrt_mul hN.le, Real.sqrt_sq hσ0]
  simp only [Function.comp, g, sqrtSumFun, smul_eq_mul, h2, Complex.real_smul]
  rw [h1', Real.sqrt_sq hσ0, sqrtAmp]
  have hexp : cexp (((-2 * Real.pi * (N * σ ^ 2) * u : ℝ)) * I) *
      cexp (((2 * Real.pi * (z * (N * σ ^ 2) + B * (Real.sqrt N * σ))) : ℝ) * I) =
      cexp (((2 * Real.pi * ((z - u) * N * σ ^ 2 + B * Real.sqrt N * σ)) : ℝ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← hexp]
  push_cast
  ring

/-! ## Non-stationary phase for `f̂` -/

/-- **Decay of `f̂`.** -/
theorem exists_fourier_sqrtSumFun_bound (p : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N z B u : ℝ, 0 < N →
    z ≠ u → |B| * Real.sqrt N ≤ 5 / 3 * (|z - u| * N) →
      ‖𝓕 (sqrtSumFun N z B) u‖ ≤ N * C / (|z - u| * N) ^ p := by
  obtain ⟨C, hC0, hC⟩ := exists_quadratic_phase_bound contDiff_sqrtAmp
    (α := 9 / 10) (β := 8 / 5) (κ := 5 / 3) (by norm_num) (by norm_num)
    (iteratedDeriv_sqrtAmp_eq_zero (Or.inl (by norm_num)))
    (iteratedDeriv_sqrtAmp_eq_zero (Or.inr (by norm_num))) p
  refine ⟨C, hC0, fun N z B u hN hzu hB => ?_⟩
  set Ξ := (z - u) * N
  have hΞ : Ξ ≠ 0 := mul_ne_zero (sub_ne_zero.2 hzu) hN.ne'
  have hΞabs : |Ξ| = |z - u| * N := by rw [abs_mul, abs_of_pos hN]
  set τ := -(B * Real.sqrt N) / Ξ
  have hτ : |τ| ≤ 5 / 3 := by
    rw [abs_div, abs_neg, abs_mul, abs_of_nonneg (Real.sqrt_nonneg N), hΞabs,
      div_le_iff₀ (by rw [← hΞabs]; exact abs_pos.2 hΞ)]
    exact hB
  rw [fourier_sqrtSumFun hN, norm_mul, Complex.norm_real, Real.norm_of_nonneg hN.le]
  have hint : ∫ σ in (9 / 10 : ℝ)..(8 / 5), sqrtAmp σ *
      cexp (((2 * Real.pi * ((z - u) * N * σ ^ 2 + B * Real.sqrt N * σ)) : ℝ) * I) =
      ∫ σ in (9 / 10 : ℝ)..(8 / 5), sqrtAmp σ * quadPhase Ξ τ σ := by
    refine intervalIntegral.integral_congr fun σ _ => ?_
    rw [quadPhase]
    congr 4
    simp only [τ, Ξ]
    field_simp
    ring
  rw [hint, mul_div_assoc, ← hΞabs]
  exact mul_le_mul_of_nonneg_left (hC Ξ τ hΞ hτ) hN.le

/-! ## Poisson summation -/

theorem isBigO_sqrtSumFun {N : ℝ} (hN : 0 < N) (z B : ℝ) :
    (sqrtSumFun N z B) =O[cocompact ℝ] fun x : ℝ => |x| ^ (-(2 : ℝ)) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [(isCompact_Icc (a := (19 / 20) ^ 2 * N) (b := (31 / 20) ^ 2 * N)).compl_mem_cocompact]
    with t ht
  rw [sqrtSumFun_eq_zero hN, norm_zero, zero_mul]
  rcases not_and_or.1 ht with h | h
  · left; push Not at h; exact h
  · right; push Not at h; exact h

theorem tsum_sqrtSumFun_eq {N : ℝ} (hN : 0 < N) (z B : ℝ)
    (hsum : Summable fun u : ℤ => 𝓕 (sqrtSumFun N z B) u) :
    ∑' n : ℤ, sqrtSumFun N z B n = ∑' u : ℤ, 𝓕 (sqrtSumFun N z B) u := by
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable (continuous_sqrtSumFun N z B)
    (by norm_num : (1 : ℝ) < 2) (isBigO_sqrtSumFun hN z B) hsum 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at h
  exact h

theorem summable_inv_one_add_abs_pow {p : ℕ} (hp : 2 ≤ p) :
    Summable fun u : ℤ => ((1 + |(u : ℝ)|) ^ p)⁻¹ := by
  have hs := (Real.summable_one_div_int_add_rpow (1 / 2) 2).2 (by norm_num)
  refine hs.of_nonneg_of_le (fun u => by positivity) fun u => ?_
  rw [one_div, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h1 : |(u : ℝ) + 1 / 2| ≤ 1 + |(u : ℝ)| := by
    calc |(u : ℝ) + 1 / 2| ≤ |(u : ℝ)| + |1 / 2| := abs_add_le _ _
      _ ≤ 1 + |(u : ℝ)| := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith
  have h2 : 0 < |(u : ℝ) + 1 / 2| := by
    rw [abs_pos]
    intro h
    have : (2 * u + 1 : ℤ) = 0 := by
      have : (2 * (u : ℝ) + 1) = 0 := by linarith
      exact_mod_cast this
    omega
  have h3 : (1 + |(u : ℝ)|) ^ 2 ≤ (1 + |(u : ℝ)|) ^ p :=
    pow_le_pow_right₀ (by linarith [abs_nonneg (u : ℝ)]) hp
  calc ((1 + |(u : ℝ)|) ^ p)⁻¹ ≤ ((1 + |(u : ℝ)|) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) h3
    _ ≤ (|(u : ℝ) + 1 / 2| ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ h2.le h1 2)

/-- `|h − cu| ≥ (1 + |u|)/3` for `0 ≤ h < c` and `h ≠ cu`. -/
theorem one_add_abs_le_three_mul {h c u : ℤ} (h0 : 0 ≤ h) (hc : h < c) (hne : h ≠ c * u) :
    1 + |u| ≤ 3 * |h - c * u| := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have hc1 : 1 ≤ c := by omega
    have : c * u ≤ u := by nlinarith
    rw [abs_of_neg hu, abs_of_pos (by nlinarith)]
    nlinarith
  · subst hu; simp only [mul_zero, sub_zero, abs_zero] at hne ⊢
    rw [abs_of_nonneg h0]; omega
  · have hc1 : 1 ≤ c := by omega
    have : c * (u - 1) ≥ u - 1 := by nlinarith
    rw [abs_of_pos hu, abs_of_neg (by nlinarith)]
    nlinarith

/-- **Poisson summation with the non-stationary terms removed.**  For `0 ≤ h < c` and
`|B| c ≤ (5/3)√N`: `|Σ_n f(n) − [h = 0] f̂_0(0)| ≤ C N (c/N)^p`. -/
theorem exists_tsum_sqrtSumFun_sub_le {p : ℕ} (hp : 2 ≤ p) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (N : ℝ) (c h : ℕ) (B : ℝ), 1 ≤ N → 1 ≤ c → h < c → |B| * c ≤ 5 / 3 * Real.sqrt N →
      ‖(∑' n : ℤ, sqrtSumFun N ((h : ℝ) / c) B n) -
          (if h = 0 then 𝓕 (sqrtSumFun N 0 B) 0 else 0)‖ ≤ C * N * ((c : ℝ) / N) ^ p := by
  obtain ⟨C₀, hC₀, hF⟩ := exists_fourier_sqrtSumFun_bound p
  set Z := ∑' u : ℤ, ((1 + |(u : ℝ)|) ^ p)⁻¹
  have hZ := summable_inv_one_add_abs_pow hp
  have hZ0 : 0 ≤ Z := tsum_nonneg fun u => by positivity
  refine ⟨C₀ * 3 ^ p * Z, by positivity, fun N c h B hN hc hhc hB => ?_⟩
  have hN0 : 0 < N := by linarith
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  set f := sqrtSumFun N ((h : ℝ) / c) B
  set K := C₀ * 3 ^ p * N * ((c : ℝ) / N) ^ p
  -- the bound away from the resonance
  have hbound : ∀ u : ℤ, (h : ℝ) / c ≠ u → ‖𝓕 f u‖ ≤ K * ((1 + |(u : ℝ)|) ^ p)⁻¹ := by
    intro u hu
    have hne : (h : ℤ) ≠ c * u := by
      intro heq
      apply hu
      rw [div_eq_iff hc0.ne']
      have : ((h : ℤ) : ℝ) = ((c * u : ℤ) : ℝ) := by rw [heq]
      push_cast at this
      linarith
    have hkey := one_add_abs_le_three_mul (Int.natCast_nonneg h) (by exact_mod_cast hhc) hne
    have hkey' : (1 + |(u : ℝ)|) / (3 * c) ≤ |(h : ℝ) / c - u| := by
      have : ((1 + |u| : ℤ) : ℝ) ≤ ((3 * |(h : ℤ) - c * u| : ℤ) : ℝ) := by exact_mod_cast hkey
      push_cast at this
      rw [show (h : ℝ) / c - u = ((h : ℝ) - c * u) / c by field_simp, abs_div, abs_of_pos hc0,
        div_le_div_iff₀ (by positivity) hc0]
      nlinarith
    have hone : 1 / (c : ℝ) ≤ |(h : ℝ) / c - u| := by
      have hk1 : (1 : ℤ) ≤ |(h : ℤ) - c * u| := Int.one_le_abs (sub_ne_zero.2 hne)
      have hk1' : (1 : ℝ) ≤ |(h : ℝ) - c * u| := by exact_mod_cast hk1
      rw [show (h : ℝ) / c - u = ((h : ℝ) - c * u) / c by field_simp, abs_div, abs_of_pos hc0]
      exact div_le_div_of_nonneg_right hk1' hc0.le
    have hBcond : |B| * Real.sqrt N ≤ 5 / 3 * (|(h : ℝ) / c - u| * N) := by
      have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
      have h1 : |B| * Real.sqrt N * c ≤ 5 / 3 * N := by
        calc |B| * Real.sqrt N * c = |B| * c * Real.sqrt N := by ring
          _ ≤ 5 / 3 * Real.sqrt N * Real.sqrt N := by gcongr
          _ = 5 / 3 * N := by rw [mul_assoc, hsq]
      have h2 : 5 / 3 * N / c ≤ 5 / 3 * (|(h : ℝ) / c - u| * N) := by
        rw [div_le_iff₀ hc0]
        have := mul_le_mul_of_nonneg_right hone (by positivity : (0 : ℝ) ≤ 5 / 3 * N * c)
        rw [div_mul_eq_mul_div, one_mul] at this
        calc 5 / 3 * N = 5 / 3 * N * c / c := by field_simp
          _ ≤ |(h : ℝ) / c - u| * (5 / 3 * N * c) := this
          _ = _ := by ring
      calc |B| * Real.sqrt N = |B| * Real.sqrt N * c / c := by field_simp
        _ ≤ 5 / 3 * N / c := by gcongr
        _ ≤ _ := h2
    refine (hF N _ B u hN0 hu hBcond).trans ?_
    have hpos : 0 < |(h : ℝ) / c - u| * N := by
      have : 0 < |(h : ℝ) / c - u| := lt_of_lt_of_le (by positivity) hone
      positivity
    have hlow : (1 + |(u : ℝ)|) / (3 * c) * N ≤ |(h : ℝ) / c - u| * N :=
      mul_le_mul_of_nonneg_right hkey' hN0.le
    have hpow := pow_le_pow_left₀ (by positivity) hlow p
    rw [div_le_iff₀ (pow_pos hpos p)]
    have h1 : (1 + |(u : ℝ)|) ≠ 0 := by positivity
    have key : (3 : ℝ) ^ p * ((c : ℝ) / N) ^ p * (N / (3 * c)) ^ p = 1 := by
      rw [← mul_pow, ← mul_pow, show (3 : ℝ) * (c / N) * (N / (3 * c)) = 1 by field_simp, one_pow]
    calc N * C₀ = C₀ * N * ((3 : ℝ) ^ p * ((c : ℝ) / N) ^ p * (N / (3 * c)) ^ p) *
          (((1 + |(u : ℝ)|) ^ p)⁻¹ * (1 + |(u : ℝ)|) ^ p) := by
          rw [key, inv_mul_cancel₀ (pow_ne_zero _ h1)]; ring
      _ = K * ((1 + |(u : ℝ)|) ^ p)⁻¹ * ((1 + |(u : ℝ)|) / (3 * c) * N) ^ p := by
          simp only [K]
          rw [show (1 + |(u : ℝ)|) / (3 * c) * N = (1 + |(u : ℝ)|) * (N / (3 * c)) by ring, mul_pow]
          ring
      _ ≤ K * ((1 + |(u : ℝ)|) ^ p)⁻¹ * (|(h : ℝ) / c - u| * N) ^ p := by gcongr
  have hK0 : 0 ≤ K := by positivity
  -- summability of the Fourier side
  have hsumF : Summable fun u : ℤ => 𝓕 f u := by
    refine Summable.of_norm_bounded_eventually (hZ.mul_left K) ?_
    refine Filter.eventually_cofinite.2 (Set.Finite.subset (Set.finite_singleton (0 : ℤ)) ?_)
    intro u hu
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hu ⊢
    by_contra hu0
    refine hu (hbound u fun hhu => ?_)
    · have : (h : ℝ) / c < 1 := by rw [div_lt_one hc0]; exact_mod_cast hhc
      have h0 : 0 ≤ (h : ℝ) / c := by positivity
      rcases lt_or_gt_of_ne hu0 with hlt | hgt
      · have : (u : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
        linarith
      · have : (1 : ℝ) ≤ u := by exact_mod_cast hgt
        linarith
  rw [tsum_sqrtSumFun_eq hN0 _ B hsumF]
  set g : ℤ → ℂ := fun u => if (h : ℝ) / c = u then 0 else 𝓕 f u
  have hg : ∀ u, ‖g u‖ ≤ K * ((1 + |(u : ℝ)|) ^ p)⁻¹ := fun u => by
    simp only [g]
    split_ifs with hu
    · rw [norm_zero]; positivity
    · exact hbound u hu
  have hgsum : Summable fun u => ‖g u‖ :=
    (hZ.mul_left K).of_nonneg_of_le (fun u => norm_nonneg _) hg
  have hsplit : (∑' u : ℤ, 𝓕 f u) - (if h = 0 then 𝓕 (sqrtSumFun N 0 B) 0 else 0) = ∑' u, g u := by
    by_cases h0 : h = 0
    · subst h0
      have hf0 : f = sqrtSumFun N 0 B := by simp [f]
      rw [if_pos rfl, hsumF.tsum_eq_add_tsum_ite 0, ← hf0, Int.cast_zero, add_sub_cancel_left]
      refine tsum_congr fun u => ?_
      simp only [g, Nat.cast_zero, zero_div]
      by_cases hu : u = 0
      · subst hu; simp
      · rw [if_neg hu, if_neg]
        exact fun h' => hu (by exact_mod_cast h'.symm)
    · rw [if_neg h0, sub_zero]
      refine tsum_congr fun u => ?_
      simp only [g]
      rw [if_neg]
      intro heq
      have h1 : (h : ℝ) / c < 1 := by rw [div_lt_one hc0]; exact_mod_cast hhc
      have h2 : 0 < (h : ℝ) / c := by
        have : (0 : ℝ) < h := by exact_mod_cast Nat.pos_of_ne_zero h0
        positivity
      rw [heq] at h1 h2
      have : (0 : ℤ) < u := by exact_mod_cast h2
      have : u < (1 : ℤ) := by exact_mod_cast h1
      omega
  rw [hsplit]
  calc ‖∑' u, g u‖ ≤ ∑' u, ‖g u‖ := norm_tsum_le_tsum_norm hgsum
    _ ≤ ∑' u : ℤ, K * ((1 + |(u : ℝ)|) ^ p)⁻¹ :=
        hgsum.tsum_le_tsum hg (hZ.mul_left K)
    _ = K * Z := tsum_mul_left
    _ = C₀ * 3 ^ p * Z * N * ((c : ℝ) / N) ^ p := by simp only [K]; ring

/-! ## The resonant term -/

/-- The resonant term `f̂_0(0) = ∫ η(√(t/N)) e(B√t) dt`. -/
def sqrtDiag (N B : ℝ) : ℂ := 𝓕 (sqrtSumFun N 0 B) 0

theorem sqrtDiag_eq {N : ℝ} (hN : 0 < N) (B : ℝ) :
    sqrtDiag N B = (N : ℂ) * ∫ σ in (9 / 10 : ℝ)..(8 / 5), sqrtAmp σ *
      cexp (((2 * Real.pi * (B * Real.sqrt N) * σ) : ℝ) * I) := by
  rw [sqrtDiag, fourier_sqrtSumFun hN]
  congr 1
  refine intervalIntegral.integral_congr fun σ _ => ?_
  congr 1; congr 1; push_cast; ring

theorem norm_sqrtDiag_le {N : ℝ} (hN : 0 < N) (B : ℝ) : ‖sqrtDiag N B‖ ≤ 3 * N := by
  rw [sqrtDiag_eq hN, norm_mul, Complex.norm_real, Real.norm_of_nonneg hN.le, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hN.le
  have hb : ∀ σ ∈ uIoc (9 / 10 : ℝ) (8 / 5), ‖sqrtAmp σ *
      cexp (((2 * Real.pi * (B * Real.sqrt N) * σ) : ℝ) * I)‖ ≤ 16 / 5 := fun σ hσ => by
    rw [uIoc_of_le (by norm_num)] at hσ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact norm_sqrtAmp_le (by linarith [hσ.1]) hσ.2
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
  norm_num [abs_of_pos]

/-- **One integration by parts** for the resonant term: `|f̂_0(0)| ≤ D √N/|B|`. -/
theorem exists_sqrtDiag_le : ∃ D : ℝ, 0 ≤ D ∧ ∀ N B : ℝ, 0 < N → B ≠ 0 →
    ‖sqrtDiag N B‖ ≤ D * Real.sqrt N / |B| := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (9 / 10 : ℝ) (8 / 5))
    (contDiff_sqrtAmp.continuous_deriv (by simp)).continuousOn
  set M' := max M 0
  refine ⟨M' * (7 / 10) / (2 * Real.pi), by positivity, fun N B hN hB => ?_⟩
  set L := B * Real.sqrt N
  have hL : L ≠ 0 := mul_ne_zero hB (Real.sqrt_pos.2 hN).ne'
  set E : ℝ → ℂ := fun σ => cexp (((2 * Real.pi * L * σ) : ℝ) * I)
  set c₀ : ℂ := (((2 * Real.pi * L : ℝ)) : ℂ) * I
  have hc₀ : c₀ ≠ 0 := mul_ne_zero (by exact_mod_cast mul_ne_zero (by positivity) hL) I_ne_zero
  have hE : ∀ σ, HasDerivAt (fun σ => c₀⁻¹ * E σ) (E σ) σ := fun σ => by
    have h1 : HasDerivAt (fun σ : ℝ => (((2 * Real.pi * L * σ) : ℝ) : ℂ) * I) c₀ σ := by
      have := (((hasDerivAt_id σ).const_mul (2 * Real.pi * L)).ofReal_comp).mul_const I
      refine this.congr_deriv ?_
      simp [c₀]
    have := (h1.cexp).const_mul c₀⁻¹
    refine this.congr_deriv ?_
    simp only [E]
    field_simp
  have hu : ∀ σ ∈ uIcc (9 / 10 : ℝ) (8 / 5), HasDerivAt sqrtAmp (deriv sqrtAmp σ) σ :=
    fun σ _ => ((contDiff_sqrtAmp.differentiable (by simp)) σ).hasDerivAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu (fun σ _ => hE σ)
    ((contDiff_sqrtAmp.continuous_deriv (by simp)).intervalIntegrable _ _)
    ((by simp only [E]; fun_prop : Continuous E).intervalIntegrable _ _)
  have h0 : sqrtAmp (9 / 10) = 0 := by
    simpa using iteratedDeriv_sqrtAmp_eq_zero (σ := 9 / 10) (Or.inl (by norm_num)) 0
  have h1 : sqrtAmp (8 / 5) = 0 := by
    simpa using iteratedDeriv_sqrtAmp_eq_zero (σ := 8 / 5) (Or.inr (by norm_num)) 0
  rw [h0, h1, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  rw [sqrtDiag_eq hN, norm_mul, Complex.norm_real, Real.norm_of_nonneg hN.le]
  change N * ‖∫ σ in (9 / 10 : ℝ)..(8 / 5), sqrtAmp σ * E σ‖ ≤ _
  rw [hibp, norm_neg]
  have hb : ∀ σ ∈ uIoc (9 / 10 : ℝ) (8 / 5), ‖deriv sqrtAmp σ * (c₀⁻¹ * E σ)‖ ≤
      M' * ‖c₀‖⁻¹ := fun σ hσ => by
    rw [uIoc_of_le (by norm_num)] at hσ
    rw [norm_mul, norm_mul, norm_inv, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact mul_le_mul_of_nonneg_right ((hM σ ⟨hσ.1.le, hσ.2⟩).trans (le_max_left _ _))
      (by positivity)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hc₀n : ‖c₀‖ = 2 * Real.pi * (|B| * Real.sqrt N) := by
    simp only [c₀, L]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_mul, abs_of_nonneg (Real.sqrt_nonneg N)]
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN.le
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hBp : 0 < |B| := abs_pos.2 hB
  calc N * ‖∫ σ in (9 / 10 : ℝ)..(8 / 5), deriv sqrtAmp σ * (c₀⁻¹ * E σ)‖
      ≤ N * (M' * ‖c₀‖⁻¹ * |8 / 5 - 9 / 10|) := by gcongr
    _ = M' * (7 / 10) / (2 * Real.pi) * Real.sqrt N / |B| := by
        rw [hc₀n, abs_of_pos (by norm_num : (0 : ℝ) < 8 / 5 - 9 / 10)]
        field_simp
        rw [Real.sq_sqrt hN.le]
        ring

end

end GaloisForLFunctions.RHTower.KuznetsovSeparation
