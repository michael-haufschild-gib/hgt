import GaloisForLFunctions.BiScaleUncertainty.KreinKantorovichMeasureTransportAndPrimePolarPairing
import GaloisForLFunctions.RHTower.EvenSectorLevyKreinRigidity

/-!
# Pillar XVII: Unconditional Derivative-Free ($S(f)$-Free) Euler–Maclaurin Cell Quadrature

This module develops **Pillar XVII** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), eliminating **Trap 1 (Spectral Second Moment $S(f)$
Divergence)** from continuum-to-discrete Euler–Maclaurin cell quadrature on the logarithmic grid and
proving **unconditional** polar quadrature bounds on `RealEvenPolarTestFn`.

## Main Results

1. **`cell_quadrature_diff_eq_shifted_integral` & `cell_quadrature_abs_diff_le_origin_collar`**:
   Everywhere-continuous Krein cell quadrature identity and bound on `[t, t + δ]` with zero
   derivative or spectral second moment $S(f)$ dependence.
2. **`nyquist_cell_origin_integral_le_levy` & `nyquist_cell_quadrature_abs_diff_le_levy`**:
   Origin-singularity absorption on the `n`-th logarithmic Nyquist cell `[log n, log(n+1)]`.
3. **`dyadic_window_global_quadrature_abs_diff_le_biScaleLevyEnergy`**:
   Global dyadic-window quadrature bound across all `N` Nyquist cells tiling `[log N, log(2N)]`,
   charging `biScaleLevyEnergy f` at most once.
4. **`RealEvenPolarTestFn.unconditional_polar_cell_quadrature_bound` &
   `RealEvenPolarTestFn.unconditional_dyadic_polar_quadrature_bound`**:
   Completely unconditional polar quadrature theorems on `RealEvenPolarTestFn` (requiring no
   hypotheses on the test function `g : RealEvenPolarTestFn` or the scale `n : ℕ`) bounding the
   discrepancy between `2(√(n+2) - √(n+1)) (weilTest g g (log(n+1))).re` and the continuum polar
   integral `∫_{log(n+1)}^{log(n+2)} e^{x/2} (weilTest g g x).re dx` directly by `weilArchRe`.
-/

open MeasureTheory Set Filter
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector
open scoped RealInnerProductSpace BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. Everywhere-Continuous $S(f)$-Free Cell Quadrature Bound -/

/-- **Exact Continuum-to-Node Cell Quadrature Identity:**
For any `f ∈ C²_c(ℝ)`, node `t ∈ ℝ`, cell width `δ ∈ ℝ`, and continuous density `ρ : ℝ → ℝ`,
$$\left(\int_t^{t+\delta} \rho(x)\,dx\right) h_f(t) - \int_t^{t+\delta} \rho(x)\,h_f(x)\,dx
  = \int_0^\delta \rho(t + y)\,\bigl(h_f(t) - h_f(t + y)\bigr)\,dy.$$ -/
theorem cell_quadrature_diff_eq_shifted_integral {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (t δ : ℝ) {ρ : ℝ → ℝ} (hρ : Continuous ρ) :
    (∫ x in t..(t + δ), ρ x) * autocorr f t - (∫ x in t..(t + δ), ρ x * autocorr f x) =
      ∫ y in (0 : ℝ)..δ, ρ (t + y) * (autocorr f t - autocorr f (t + y)) := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hshift1 := intervalIntegral_collar_shift ρ t δ
  have hshift2 := intervalIntegral_collar_shift (fun x : ℝ => ρ x * autocorr f x) t δ
  rw [← hshift1, ← hshift2]
  have hint1 : IntervalIntegrable (fun y : ℝ => ρ (t + y) * autocorr f t) volume 0 δ :=
    ((hρ.comp (continuous_const.add continuous_id)).mul continuous_const).intervalIntegrable 0 δ
  have hint2 : IntervalIntegrable (fun y : ℝ => ρ (t + y) * autocorr f (t + y)) volume 0 δ :=
    ((hρ.comp (continuous_const.add continuous_id)).mul
      (hc.comp (continuous_const.add continuous_id))).intervalIntegrable 0 δ
  rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_sub hint1 hint2]
  refine intervalIntegral.integral_congr fun y _ => by ring

/-- **Pointwise $S(f)$-Free Krein Cell Quadrature Bound:**
For any continuous compactly supported `f : ℝ → ℝ`, any `t, y ∈ ℝ`, any weight `W₀ > 0`, and any
`ρ_val ≥ 0`,
$$\rho_{\mathrm{val}}\,\bigl|h_f(t) - h_f(t + y)\bigr|
  \;\le\; W_0\bigl(h_f(0) - h_f(y)\bigr) + \frac{\rho_{\mathrm{val}}^2}{2 W_0}\,h_f(0).$$ -/
theorem pointwise_weighted_krein_cell_bound {f : ℝ → ℝ} (hfc : HasCompactSupport f)
    (hf : Continuous f) {W₀ ρ_val : ℝ} (hW₀ : 0 < W₀) (hρ : 0 ≤ ρ_val) (t y : ℝ) :
    ρ_val * |autocorr f t - autocorr f (t + y)| ≤
      W₀ * (autocorr f 0 - autocorr f y) + ρ_val ^ 2 / (2 * W₀) * autocorr f 0 := by
  have hR : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have hD : 0 ≤ autocorr f 0 - autocorr f y := autocorr_sub_nonneg hfc hf y
  have hkrein : |autocorr f t - autocorr f (t + y)| ≤
      Real.sqrt (2 * autocorr f 0 * (autocorr f 0 - autocorr f y)) := by
    rw [abs_sub_comm]
    exact abs_autocorr_add_sub_le_sqrt hfc hf t y
  have hmul := mul_le_mul_of_nonneg_left hkrein hρ
  have hyoung := signed_collar_young_bound (w := ρ_val) hW₀ hR hD
  linarith

/-- **Single-Cell Derivative-Free ($S(f)$-Free) Euler–Maclaurin Quadrature Inequality:**
For any `f ∈ C²_c(ℝ)`, node `t ∈ ℝ`, width `δ ≥ 0`, parameter `W₀ > 0`, and continuous density
`ρ : ℝ → ℝ` with `ρ ≥ 0` on `[t, t + δ]`,
$$\left|\left(\int_t^{t+\delta} \rho(x)\,dx\right) h_f(t) - \int_t^{t+\delta} \rho(x)\,h_f(x)\,dx\right|
  \;\le\; W_0 \int_0^\delta \bigl(h_f(0) - h_f(y)\bigr)\,dy
    + \frac{h_f(0)}{2 W_0}\int_t^{t+\delta} \rho(x)^2\,dx.$$ -/
theorem cell_quadrature_abs_diff_le_origin_collar {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (t : ℝ) {δ W₀ : ℝ} (hδ : 0 ≤ δ) (hW₀ : 0 < W₀)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ_nn : ∀ x ∈ Icc t (t + δ), 0 ≤ ρ x) :
    |(∫ x in t..(t + δ), ρ x) * autocorr f t - ∫ x in t..(t + δ), ρ x * autocorr f x| ≤
      W₀ * (∫ y in (0 : ℝ)..δ, (autocorr f 0 - autocorr f y)) +
        autocorr f 0 / (2 * W₀) * ∫ x in t..(t + δ), (ρ x) ^ 2 := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  rw [cell_quadrature_diff_eq_shifted_integral hf hfc t δ hρ]
  have habs_le :
      |∫ y in (0 : ℝ)..δ, ρ (t + y) * (autocorr f t - autocorr f (t + y))| ≤
        ∫ y in (0 : ℝ)..δ, |ρ (t + y) * (autocorr f t - autocorr f (t + y))| :=
    intervalIntegral.abs_integral_le_integral_abs hδ
  have hint_lhs : IntervalIntegrable
      (fun y : ℝ => |ρ (t + y) * (autocorr f t - autocorr f (t + y))|) volume 0 δ :=
    (((hρ.comp (continuous_const.add continuous_id)).mul
      (continuous_const.sub (hc.comp (continuous_const.add continuous_id)))).abs).intervalIntegrable 0 δ
  have hint_orig : IntervalIntegrable (fun y : ℝ => autocorr f 0 - autocorr f y) volume 0 δ :=
    (continuous_const.sub hc).intervalIntegrable 0 δ
  have hint_rho2 : IntervalIntegrable (fun y : ℝ => (ρ (t + y)) ^ 2) volume 0 δ :=
    ((hρ.comp (continuous_const.add continuous_id)).pow 2).intervalIntegrable 0 δ
  have hmono :
      (∫ y in (0 : ℝ)..δ, |ρ (t + y) * (autocorr f t - autocorr f (t + y))|) ≤
        ∫ y in (0 : ℝ)..δ,
          (W₀ * (autocorr f 0 - autocorr f y) +
            (autocorr f 0 / (2 * W₀)) * (ρ (t + y)) ^ 2) := by
    refine intervalIntegral.integral_mono_on hδ hint_lhs
      ((hint_orig.const_mul W₀).add (hint_rho2.const_mul (autocorr f 0 / (2 * W₀)))) fun y hy => ?_
    have hρy : 0 ≤ ρ (t + y) := hρ_nn (t + y) ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rw [abs_mul, abs_of_nonneg hρy]
    have hpt := pointwise_weighted_krein_cell_bound hfc hf.continuous hW₀ hρy t y
    have hring : ρ (t + y) ^ 2 / (2 * W₀) * autocorr f 0 =
        autocorr f 0 / (2 * W₀) * ρ (t + y) ^ 2 := by ring
    linarith
  rw [intervalIntegral.integral_add (hint_orig.const_mul W₀)
      (hint_rho2.const_mul (autocorr f 0 / (2 * W₀))),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  have hshift_sq := intervalIntegral_collar_shift (fun x : ℝ => (ρ x) ^ 2) t δ
  rw [hshift_sq] at hmono
  linarith

/-! ## §2. Origin-Singularity Absorption on Logarithmic Nyquist Cells -/

/-- **Origin-Singularity Absorption on the `n`-th Nyquist Cell (`n ≥ 1`):**
For any `f ∈ C²_c(ℝ)` and `n ≥ 1`, since `archLevySinhWeight y ≥ n` on
`(0, log(n + 1) - log n]`,
$$\int_0^{\log(n+1) - \log n} \bigl(h_f(0) - h_f(y)\bigr)\,dy
  \;\le\; \frac{1}{n}\int_{Ioc\,0\,(\log(n+1) - \log n)} \bigl(h_f(0) - h_f(y)\bigr)\,\operatorname{archLevySinhWeight}(y)\,dy.$$ -/
theorem nyquist_cell_origin_integral_le_levy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {n : ℕ} (hn : 1 ≤ n) :
    (∫ y in (0 : ℝ)..(Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)),
        (autocorr f 0 - autocorr f y)) ≤
      (1 / (n : ℝ)) *
        ∫ y in Ioc 0 (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)),
          (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  set δ_n := Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)
  have hδn_pos : 0 < δ_n := log_succ_sub_log_pos hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hint_levy :
      IntegrableOn (fun y => (autocorr f 0 - autocorr f y) * archLevySinhWeight y) (Ioc 0 δ_n) :=
    (integrableOn_biScaleLevyIntegrand hf hfc).mono_set (fun y hy => hy.1)
  rw [intervalIntegral.integral_of_le hδn_pos.le, ← integral_const_mul]
  refine setIntegral_mono_ae_restrict
    ((continuous_const.sub hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hint_levy.const_mul (1 / (n : ℝ))) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  have hge : (n : ℝ) ≤ archLevySinhWeight y :=
    archLevySinhWeight_ge_nat_on_nyquist_collar hn hy.1 hy.2
  have h1 : 1 ≤ (1 / (n : ℝ)) * archLevySinhWeight y := by
    rw [one_div_mul_eq_div, one_le_div hn_pos]
    exact hge
  have hnonneg : 0 ≤ autocorr f 0 - autocorr f y :=
    autocorr_sub_nonneg hfc hf.continuous y
  calc
    autocorr f 0 - autocorr f y = (autocorr f 0 - autocorr f y) * 1 := (mul_one _).symm
    _ ≤ (autocorr f 0 - autocorr f y) * ((1 / (n : ℝ)) * archLevySinhWeight y) :=
      mul_le_mul_of_nonneg_left h1 hnonneg
    _ = (1 / (n : ℝ)) * ((autocorr f 0 - autocorr f y) * archLevySinhWeight y) := by ring

/-- **Nyquist Cell $S(f)$-Free Euler–Maclaurin Quadrature Bound (`n ≥ 1`):**
For any `f ∈ C²_c(ℝ)`, `n ≥ 1`, parameter `η > 0`, and continuous density `ρ : ℝ → ℝ` with
`ρ ≥ 0` on `[log n, log(n + 1)]`, setting `W₀ = η * n` in `cell_quadrature_abs_diff_le_origin_collar`
absorbs the factor of `n` into `archLevySinhWeight`:
$$\left|\left(\int_{\log n}^{\log(n+1)} \rho(x)\,dx\right) h_f(\log n) - \int_{\log n}^{\log(n+1)} \rho(x)\,h_f(x)\,dx\right|
  \;\le\; \eta \int_{Ioc\,0\,\delta_n} \bigl(h_f(0) - h_f(y)\bigr)\,\operatorname{archLevySinhWeight}(y)\,dy
    + \frac{h_f(0)}{2 \eta n}\int_{\log n}^{\log(n+1)} \rho(x)^2\,dx.$$ -/
theorem nyquist_cell_quadrature_abs_diff_le_levy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {n : ℕ} (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hρ_nn : ∀ x ∈ Icc (Real.log (n : ℝ)) (Real.log ((n + 1 : ℕ) : ℝ)), 0 ≤ ρ x) :
    |(∫ x in Real.log (n : ℝ)..Real.log ((n + 1 : ℕ) : ℝ), ρ x) *
        autocorr f (Real.log (n : ℝ)) -
      ∫ x in Real.log (n : ℝ)..Real.log ((n + 1 : ℕ) : ℝ), ρ x * autocorr f x| ≤
      η * (∫ y in Ioc 0 (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)),
          (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
        autocorr f 0 / (2 * η * (n : ℝ)) *
          ∫ x in Real.log (n : ℝ)..Real.log ((n + 1 : ℕ) : ℝ), (ρ x) ^ 2 := by
  set tn := Real.log (n : ℝ)
  set δn := Real.log ((n + 1 : ℕ) : ℝ) - tn
  have htn_add : tn + δn = Real.log ((n + 1 : ℕ) : ℝ) := add_sub_cancel _ _
  have hδn_pos : 0 < δn := log_succ_sub_log_pos hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hW₀_pos : 0 < η * (n : ℝ) := mul_pos hη hn_pos
  have hρ_nn' : ∀ x ∈ Icc tn (tn + δn), 0 ≤ ρ x := by
    rw [htn_add]; exact hρ_nn
  have hcell := cell_quadrature_abs_diff_le_origin_collar hf hfc tn hδn_pos.le hW₀_pos hρ hρ_nn'
  rw [htn_add] at hcell
  have habsorb := nyquist_cell_origin_integral_le_levy hf hfc hn
  have hmul := mul_le_mul_of_nonneg_left habsorb hW₀_pos.le
  have hcancel :
      (η * (n : ℝ)) * ((1 / (n : ℝ)) *
        ∫ y in Ioc 0 δn, (autocorr f 0 - autocorr f y) * archLevySinhWeight y) =
      η * ∫ y in Ioc 0 δn, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
    field_simp [hn_pos.ne']
  rw [hcancel] at hmul
  have hdiv_eq : 2 * (η * (n : ℝ)) = 2 * η * (n : ℝ) := by ring
  rw [hdiv_eq] at hcell
  linarith

/-! ## §3. Dyadic-Window Global Euler–Maclaurin Quadrature Theorem on `[log N, log(2N)]` -/

/-- Adjacent-interval telescoping identity across the `N` Nyquist cells tiling `[log N, log(2N)]`:
`∑ k ∈ range N, ∫ x in log(N+k)..log(N+k+1), F x = ∫ x in log N..log(2N), F x`. -/
theorem sum_nyquist_cell_integral_eq_dyadic_window {F : ℝ → ℝ} (hF : Continuous F) (N : ℕ) :
    (∑ k ∈ Finset.range N,
        ∫ x in Real.log ((N + k : ℕ) : ℝ)..Real.log ((N + k + 1 : ℕ) : ℝ), F x) =
      ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), F x := by
  rw [intervalIntegral_dyadic_log_partition_eq hF N]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hshift := intervalIntegral_collar_shift F (Real.log ((N + k : ℕ) : ℝ))
    (Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ))
  have hadd :
      Real.log ((N + k : ℕ) : ℝ) +
        (Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)) =
        Real.log ((N + k + 1 : ℕ) : ℝ) := add_sub_cancel _ _
  rw [hadd] at hshift
  exact hshift.symm

/-- **Sum of Nyquist Cell Quadrature Errors on `[log N, log(2N)]` (`S(f)`-Free):**
Across all `N` Nyquist cells `[log(N+k), log(N+k+1)]` (`0 ≤ k < N`, `N ≥ 1`), the sum of the
absolute cell quadrature errors is controlled by **a single copy** of the origin Lévy collar
integral on `(0, log(N+1) - log N]` plus the dyadic-window `L²` norm of `ρ`. -/
theorem dyadic_window_sum_cell_quadrature_abs_diff_le_levy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ_nn : ∀ x : ℝ, 0 ≤ ρ x) :
    ∑ k ∈ Finset.range N,
        |(∫ x in Real.log ((N + k : ℕ) : ℝ)..Real.log ((N + k + 1 : ℕ) : ℝ), ρ x) *
            autocorr f (Real.log ((N + k : ℕ) : ℝ)) -
          ∫ x in Real.log ((N + k : ℕ) : ℝ)..Real.log ((N + k + 1 : ℕ) : ℝ),
            ρ x * autocorr f x| ≤
      η * (∫ y in Ioc 0 (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)),
          (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
        autocorr f 0 / (2 * η) *
          ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (ρ x) ^ 2 := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  set δ_N := Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hint_levy :
      IntegrableOn (fun y => (autocorr f 0 - autocorr f y) * archLevySinhWeight y) (Ioc 0 δ_N) :=
    (integrableOn_biScaleLevyIntegrand hf hfc).mono_set (fun y hy => hy.1)
  have hk_bound : ∀ k ∈ Finset.range N,
      |(∫ x in Real.log ((N + k : ℕ) : ℝ)..Real.log ((N + k + 1 : ℕ) : ℝ), ρ x) *
          autocorr f (Real.log ((N + k : ℕ) : ℝ)) -
        ∫ x in Real.log ((N + k : ℕ) : ℝ)..Real.log ((N + k + 1 : ℕ) : ℝ),
          ρ x * autocorr f x| ≤
        (η / (N : ℝ)) *
          (∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
          autocorr f 0 / (2 * η) *
            ∫ x in Real.log ((N + k : ℕ) : ℝ)..Real.log ((N + k + 1 : ℕ) : ℝ), (ρ x) ^ 2 := by
    intro k _
    set tk := Real.log ((N + k : ℕ) : ℝ)
    set δk := Real.log ((N + k + 1 : ℕ) : ℝ) - tk
    have hNk : 1 ≤ N + k := by omega
    have hδk_pos : 0 < δk := log_succ_sub_log_pos hNk
    have hδk_le_δN : δk ≤ δ_N := log_succ_sub_log_antitone hN (by omega)
    have htk_add : tk + δk = Real.log ((N + k + 1 : ℕ) : ℝ) := add_sub_cancel _ _
    have hcell := cell_quadrature_abs_diff_le_origin_collar hf hfc tk hδk_pos.le hη hρ
      (fun x _ => hρ_nn x)
    rw [htk_add] at hcell
    have habs_k := nyquist_cell_origin_integral_le_levy hf hfc hNk
    have hmono_set :
        (∫ y in Ioc 0 δk, (autocorr f 0 - autocorr f y) * archLevySinhWeight y) ≤
          ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
      refine setIntegral_mono_set hint_levy ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        exact mul_nonneg (autocorr_sub_nonneg hfc hf.continuous y) (archLevySinhWeight_pos hy.1).le
      · refine Eventually.of_forall fun y hy => ⟨hy.1, le_trans hy.2 hδk_le_δN⟩
    have hinv_le : 1 / ((N + k : ℕ) : ℝ) ≤ 1 / (N : ℝ) := by
      refine one_div_le_one_div_of_le hN_pos ?_
      exact_mod_cast (by omega : N ≤ N + k)
    have hlev_nn :
        0 ≤ ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
      refine setIntegral_nonneg measurableSet_Ioc fun y hy => ?_
      exact mul_nonneg (autocorr_sub_nonneg hfc hf.continuous y) (archLevySinhWeight_pos hy.1).le
    have horig_le :
        (∫ y in (0 : ℝ)..δk, (autocorr f 0 - autocorr f y)) ≤
          (1 / (N : ℝ)) *
            ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
      calc
        (∫ y in (0 : ℝ)..δk, (autocorr f 0 - autocorr f y))
            ≤ (1 / ((N + k : ℕ) : ℝ)) *
                ∫ y in Ioc 0 δk, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := habs_k
        _ ≤ (1 / ((N + k : ℕ) : ℝ)) *
                ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y :=
              mul_le_mul_of_nonneg_left hmono_set (by positivity)
        _ ≤ (1 / (N : ℝ)) *
                ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y :=
              mul_le_mul_of_nonneg_right hinv_le hlev_nn
    have hmul := mul_le_mul_of_nonneg_left horig_le hη.le
    have hrew :
        η * ((1 / (N : ℝ)) *
          ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y) =
        (η / (N : ℝ)) *
          ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
      ring
    linarith
  have hsum := Finset.sum_le_sum hk_bound
  have htel := sum_nyquist_cell_integral_eq_dyadic_window (F := fun x => (ρ x) ^ 2) (hρ.pow 2) N
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum, htel] at hsum
  have hcancel :
      (N : ℝ) * ((η / (N : ℝ)) *
        ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y) =
      η * ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
    field_simp [hN_pos.ne']
  linarith

/-- **Global Dyadic-Window Euler–Maclaurin Quadrature Inequality (`S(f)`-Free):**
For any `f ∈ C²_c(ℝ)`, `N ≥ 1`, `η > 0`, and continuous nonnegative `ρ : ℝ → ℝ`, the discrepancy
between the discrete Nyquist quadrature sum and the continuum integral over `[log N, log(2N)]`
is controlled by a single copy of the origin Lévy collar plus the dyadic `L²` norm of `ρ`. -/
theorem dyadic_window_global_quadrature_abs_diff_le_levy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ_nn : ∀ x : ℝ, 0 ≤ ρ x) :
    |(∑ k ∈ Finset.range N,
        (∫ x in Real.log ((N + k : ℕ) : ℝ)..Real.log ((N + k + 1 : ℕ) : ℝ), ρ x) *
          autocorr f (Real.log ((N + k : ℕ) : ℝ))) -
      ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), ρ x * autocorr f x| ≤
      η * (∫ y in Ioc 0 (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)),
          (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
        autocorr f 0 / (2 * η) *
          ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (ρ x) ^ 2 := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have htel := sum_nyquist_cell_integral_eq_dyadic_window
    (F := fun x => ρ x * autocorr f x) (hρ.mul hc) N
  rw [← htel, ← Finset.sum_sub_distrib]
  exact le_trans (Finset.abs_sum_le_sum_abs _ _)
    (dyadic_window_sum_cell_quadrature_abs_diff_le_levy hf hfc hN hη hρ hρ_nn)

/-- Corollary bounding the global dyadic-window quadrature error directly by `biScaleLevyEnergy f`. -/
theorem dyadic_window_global_quadrature_abs_diff_le_biScaleLevyEnergy {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ_nn : ∀ x : ℝ, 0 ≤ ρ x) :
    |(∑ k ∈ Finset.range N,
        (∫ x in Real.log ((N + k : ℕ) : ℝ)..Real.log ((N + k + 1 : ℕ) : ℝ), ρ x) *
          autocorr f (Real.log ((N + k : ℕ) : ℝ))) -
      ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), ρ x * autocorr f x| ≤
      η * biScaleLevyEnergy f +
        autocorr f 0 / (2 * η) *
          ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (ρ x) ^ 2 := by
  refine le_trans (dyadic_window_global_quadrature_abs_diff_le_levy hf hfc hN hη hρ hρ_nn) ?_
  have hmono :
      (∫ y in Ioc 0 (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)),
          (autocorr f 0 - autocorr f y) * archLevySinhWeight y) ≤
        biScaleLevyEnergy f := by
    unfold biScaleLevyEnergy
    refine setIntegral_mono_set (integrableOn_biScaleLevyIntegrand hf hfc) ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact mul_nonneg (autocorr_sub_nonneg hfc hf.continuous y) (archLevySinhWeight_pos hy).le
    · exact Eventually.of_forall fun y hy => hy.1
  have hmul := mul_le_mul_of_nonneg_left hmono hη.le
  linarith

/-! ## §4. Exact Polar Cell Integrals & Unconditional `RealEvenPolarTestFn` Quadrature -/

/-- Exact closed form of the polar cell weight on `[log n, log(n + 1)]` (`n ≥ 1`):
`∫ x in log n..log(n + 1), exp(x / 2) = 2 * (√(n + 1) - √n)`. -/
theorem integral_exp_half_log_cell_eq {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in Real.log (n : ℝ)..Real.log ((n + 1 : ℕ) : ℝ), Real.exp (x / 2)) =
      2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hderiv : ∀ x ∈ uIcc (Real.log (n : ℝ)) (Real.log ((n + 1 : ℕ) : ℝ)),
      HasDerivAt (fun u : ℝ => 2 * Real.exp (u / 2)) (Real.exp (x / 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) x := by
      simpa using (hasDerivAt_id x).div_const 2
    have h2 := (Real.hasDerivAt_exp (x / 2)).comp x h1
    have h3 := h2.const_mul 2
    have h4 : 2 * (Real.exp (x / 2) * (1 / 2)) = Real.exp (x / 2) := by ring
    rwa [h4] at h3
  have hint : IntervalIntegrable (fun x : ℝ => Real.exp (x / 2)) volume
      (Real.log (n : ℝ)) (Real.log ((n + 1 : ℕ) : ℝ)) :=
    (Real.continuous_exp.comp (continuous_id.div_const 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    exp_half_log_eq_sqrt hn1_pos, exp_half_log_eq_sqrt hn_pos]
  ring

/-- Exact unit normalization of the squared polar density `(exp(x / 2))² = exp x` on every Nyquist
cell `[log n, log(n + 1)]` (`n ≥ 1`):
`∫ x in log n..log(n + 1), (exp(x / 2))² = 1`. -/
theorem integral_exp_half_sq_log_cell_eq {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in Real.log (n : ℝ)..Real.log ((n + 1 : ℕ) : ℝ), (Real.exp (x / 2)) ^ 2) = 1 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hsq : (fun x : ℝ => (Real.exp (x / 2)) ^ 2) = Real.exp := by
    funext x
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [hsq, integral_exp, Real.exp_log hn1_pos, Real.exp_log hn_pos]
  push_cast
  ring

/-- **Exact $S(f)$-Free Polar Nyquist Cell Quadrature Inequality (`n ≥ 1`):**
For any `f ∈ C²_c(ℝ)`, `n ≥ 1`, and `η > 0`,
$$\left|2\bigl(\sqrt{n+1} - \sqrt{n}\bigr)\,h_f(\log n) - \int_{\log n}^{\log(n+1)} e^{x/2}\,h_f(x)\,dx\right|
  \;\le\; \eta \int_{Ioc\,0\,(\log(n+1) - \log n)} \bigl(h_f(0) - h_f(y)\bigr)\,\operatorname{archLevySinhWeight}(y)\,dy
    + \frac{h_f(0)}{2 \eta n}.$$ -/
theorem nyquist_polar_cell_quadrature_abs_diff_le_levy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {n : ℕ} (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η) :
    |2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) * autocorr f (Real.log (n : ℝ)) -
      ∫ x in Real.log (n : ℝ)..Real.log ((n + 1 : ℕ) : ℝ),
        Real.exp (x / 2) * autocorr f x| ≤
      η * (∫ y in Ioc 0 (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)),
          (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
        autocorr f 0 / (2 * η * (n : ℝ)) := by
  have hcont : Continuous (fun x : ℝ => Real.exp (x / 2)) :=
    Real.continuous_exp.comp (continuous_id.div_const 2)
  have hcell := nyquist_cell_quadrature_abs_diff_le_levy hf hfc hn hη hcont
    (fun x _ => (Real.exp_pos (x / 2)).le)
  rw [integral_exp_half_log_cell_eq hn, integral_exp_half_sq_log_cell_eq hn, mul_one] at hcell
  exact hcell

/-- **Unconditional Polar Nyquist Cell Quadrature Bound on `RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn` and EVERY `n : ℕ` (with zero hypotheses on `g` or `n`),
$$\left|2\bigl(\sqrt{n+2} - \sqrt{n+1}\bigr)\,(\operatorname{weilTest}\,g\,g\,(\log(n+1))).\mathrm{re}
  - \int_{\log(n+1)}^{\log(n+2)} e^{x/2}\,(\operatorname{weilTest}\,g\,g\,x).\mathrm{re}\,dx\right|$$
$$\le\; \operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
  + \left(|\Omega(0)| + \frac{1}{2(n+1)}\right)(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}.$$ -/
theorem RealEvenPolarTestFn.unconditional_polar_cell_quadrature_bound
    (g : RealEvenPolarTestFn) (n : ℕ) :
    |2 * (Real.sqrt ((n + 2 : ℕ) : ℝ) - Real.sqrt ((n + 1 : ℕ) : ℝ)) *
        (EF.weilTest g.1.1.1 g.1.1.1 (Real.log ((n + 1 : ℕ) : ℝ))).re -
      ∫ x in Real.log ((n + 1 : ℕ) : ℝ)..Real.log ((n + 2 : ℕ) : ℝ),
        Real.exp (x / 2) * (EF.weilTest g.1.1.1 g.1.1.1 x).re| ≤
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
        (|EF.gammaBracket 0| + 1 / (2 * ((n + 1 : ℕ) : ℝ))) *
          (EF.weilTest g.1.1.1 g.1.1.1 0).re := by
  have hn1 : 1 ≤ n + 1 := by omega
  have hcell := nyquist_polar_cell_quadrature_abs_diff_le_levy
    g.contDiff_source g.hasCompactSupport_source hn1 one_pos
  have hnat : n + 1 + 1 = n + 2 := rfl
  rw [hnat] at hcell
  have hmono :
      (∫ y in Ioc 0 (Real.log ((n + 2 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)),
          (autocorr g.source 0 - autocorr g.source y) * archLevySinhWeight y) ≤
        biScaleLevyEnergy g.source := by
    unfold biScaleLevyEnergy
    refine setIntegral_mono_set
      (integrableOn_biScaleLevyIntegrand g.contDiff_source g.hasCompactSupport_source) ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact mul_nonneg
        (autocorr_sub_nonneg g.hasCompactSupport_source g.contDiff_source.continuous y)
        (archLevySinhWeight_pos hy).le
    · exact Eventually.of_forall fun y hy => hy.1
  have hlev_eq :
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) =
        EF.gammaBracket 0 * autocorr g.source 0 + biScaleLevyEnergy g.source := by
    rw [g.weilArchRe_eq_levy, ← g.autocorr_eq 0]
    congr 1
    unfold biScaleLevyEnergy archLevySinhWeight
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [g.autocorr_eq 0, g.autocorr_eq x]
  have hgamma : |EF.gammaBracket 0| = -EF.gammaBracket 0 := by
    rw [abs_gammaBracket_zero, gammaBracket_zero_eq]
    ring
  have hint_eq :
      (∫ x in Real.log ((n + 1 : ℕ) : ℝ)..Real.log ((n + 2 : ℕ) : ℝ),
          Real.exp (x / 2) * (EF.weilTest g.1.1.1 g.1.1.1 x).re) =
        ∫ x in Real.log ((n + 1 : ℕ) : ℝ)..Real.log ((n + 2 : ℕ) : ℝ),
          Real.exp (x / 2) * autocorr g.source x := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [g.autocorr_eq x]
  rw [← g.autocorr_eq (Real.log ((n + 1 : ℕ) : ℝ)), ← g.autocorr_eq 0, hint_eq, hgamma, hlev_eq]
  have hring :
      autocorr g.source 0 / (2 * 1 * ((n + 1 : ℕ) : ℝ)) =
        1 / (2 * ((n + 1 : ℕ) : ℝ)) * autocorr g.source 0 := by
    ring
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
