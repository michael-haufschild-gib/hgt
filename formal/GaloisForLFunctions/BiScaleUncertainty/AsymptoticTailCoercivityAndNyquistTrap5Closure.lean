import GaloisForLFunctions.BiScaleUncertainty.ProducerConsumerDualityAndNymanBeurlingBridge

/-!
# Pillar XIII: Asymptotic Tail Coercivity & Infinite-Grid Closure of Trap 5

This module develops **Pillar XIII** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**,
addressing the third core requirement for overcoming **Wall 1** (`docs/reports/wall1.md`) and
closing **Trap 5** (`DistantCopyPolarEnforcement.lean`) on the infinite logarithmic grid
$\Lambda_{\log} = \{\log n : n \ge 2\}$.

## Mathematical Mechanism: Why the Infinite Logarithmic Grid Defeats Distant Polar Copies

In `DistantCopyPolarEnforcement.lean` (Trap 5), when only **finitely many** grid zeros
$h_f(\log n) = 0$ ($2 \le n \le N_0$) are imposed, a translated copy
$\operatorname{polarCopy}(f_0, T)(u) = f_0(u) - e^{-T/2} f_0(u - T)$ at a distant scale
$T \gg \log N_0$ enforces the hyperbolic polar constraint $\int_0^\infty h(x)\cosh(x/2)\,dx = 0$
by placing negative polar lobe mass $\int h^-(x)\cosh(x/2)\,dx \asymp \frac{1}{2} h_{f_0}(0)$ at
scale $T$ with **uniformly bounded kinetic energy** $K = O(1)$ as $T \to \infty$.

When the logarithmic grid zeros $h_f(\log n) = 0$ are active in the dyadic window
$[\log N, \log(2N)]$ at scale $T = \log N$, the $N$ consecutive grid nodes
$\log N < \log(N+1) < \dots < \log(2N)$ have Nyquist spacing
$$\delta_k = \log(N+k+1) - \log(N+k) \le \frac{1}{N} = e^{-T}.$$
1. Under any quadratic origin-collar regularity $h_f(0) - h_f(y) \le K y^2$ on $[0, 1/N]$,
   Krein's Nyquist compression (Pillar XI) forces the $L^2$ correlation energy on
   $[\log N, \log(2N)]$ to decay as $O(N^{-2})$:
   $$\int_{\log N}^{\log(2N)} h_f(x)^2\,dx \;\le\; \frac{2 K}{N^2}\,h_f(0).$$
2. Meanwhile, the squared hyperbolic polar weight on $[\log N, \log(2N)]$ grows only as $O(N)$:
   $$\int_{\log N}^{\log(2N)} \cosh(x/2)^2\,dx \;\le\; 2 N \log 2.$$
3. By Cauchy–Schwarz (`intervalIntegral_cauchy_schwarz_sq_le` from Pillar XII), the net polar
   $\cosh(x/2)$-mass on $[\log N, \log(2N)]$ decays as $O(N^{-1/2}) = O(e^{-T/2})$:
   $$\left(\int_{\log N}^{\log(2N)} |h_f(x)|\,\cosh(x/2)\,dx\right)^2 \;\le\; \frac{4 \log 2}{N}\,K\,h_f(0) \;\xrightarrow{N \to \infty}\; 0.$$
4. Consequently (**`infinite_grid_distant_lobe_kinetic_coercivity`**), any state that places
   negative polar lobe mass $\mu \le \int_{\log N}^{\log(2N)} h_f^-(x)\cosh(x/2)\,dx$ inside
   $[\log N, \log(2N)]$ is forced by the $N$ Nyquist-packed grid zeros to pay kinetic energy
   growing at least linearly in $N = e^T$:
   $$N\,\mu^2 \;\le\; 4 \log 2 \, K \, h_f(0).$$
-/

namespace GaloisForLFunctions.BiScaleUncertainty

open MeasureTheory Set Filter
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open scoped BigOperators

noncomputable section

/-! ## §1. Quadratic Origin-Collar Bound & `O(N⁻²)` Dyadic-Window `L²` Decay -/

/-- If `0 ≤ δ`, `0 ≤ K`, and `autocorr f 0 - autocorr f y ≤ K * y²` on `Icc 0 δ`, then
`∫ y in 0..δ, (autocorr f 0 - autocorr f y) ≤ K * δ³`. -/
theorem integral_autocorr_sub_le_cube_of_quad_collar {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {δ K : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hquad : ∀ y ∈ Icc 0 δ, autocorr f 0 - autocorr f y ≤ K * y ^ 2) :
    (∫ y in (0 : ℝ)..δ, (autocorr f 0 - autocorr f y)) ≤ K * δ ^ 3 := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hint1 : IntervalIntegrable (fun y => autocorr f 0 - autocorr f y) volume 0 δ :=
    (continuous_const.sub hc).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun _ : ℝ => K * δ ^ 2) volume 0 δ :=
    intervalIntegrable_const
  have hmono :
      (∫ y in (0 : ℝ)..δ, (autocorr f 0 - autocorr f y)) ≤
        ∫ _y in (0 : ℝ)..δ, K * δ ^ 2 := by
    refine intervalIntegral.integral_mono_on hδ hint1 hint2 fun y hy => ?_
    have hy_sq : y ^ 2 ≤ δ ^ 2 := by
      nlinarith [hy.1, hy.2]
    exact le_trans (hquad y hy) (mul_le_mul_of_nonneg_left hy_sq hK)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
  calc
    (∫ y in (0 : ℝ)..δ, (autocorr f 0 - autocorr f y)) ≤ δ * (K * δ ^ 2) := hmono
    _ = K * δ ^ 3 := by ring

/-- **`O(N⁻²)` Dyadic-Window `L²` Decay under Quadratic Origin-Collar Regularity:**
If `f ∈ C²_c(ℝ)` vanishes at the `N` dyadic-window grid nodes `log(N + k)` (`0 ≤ k < N`, `N ≥ 1`)
and satisfies `autocorr f 0 - autocorr f y ≤ K * y²` on `[0, 1 / N]` (`0 ≤ K`), then
`∫ x in log N..log(2N), (autocorr f x)² ≤ (2 * K / N²) * autocorr f 0`. -/
theorem integral_autocorr_sq_dyadic_window_le_of_quad_collar {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {N : ℕ} (hN : 1 ≤ N)
    (hzeros : ∀ k ∈ Finset.range N, autocorr f (Real.log ((N + k : ℕ) : ℝ)) = 0)
    {K : ℝ} (hK : 0 ≤ K)
    (hquad : ∀ y ∈ Icc 0 (1 / (N : ℝ)), autocorr f 0 - autocorr f y ≤ K * y ^ 2) :
    (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (autocorr f x) ^ 2) ≤
      (2 * K / (N : ℝ) ^ 2) * autocorr f 0 := by
  have hbase := integral_autocorr_sq_dyadic_window_le_sum_collar hf hfc hN hzeros
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk_le : ∀ k ∈ Finset.range N,
      (∫ y in (0 : ℝ)..(Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)),
        (autocorr f 0 - autocorr f y)) ≤ K * (1 / (N : ℝ)) ^ 3 := by
    intro k _
    set δ_k := Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)
    have hNk : 1 ≤ N + k := by omega
    have hδk_pos : 0 < δ_k := log_succ_sub_log_pos hNk
    have hδk_le_inv : δ_k ≤ 1 / (N : ℝ) := by
      have h1 := log_succ_sub_log_antitone hN (n := N + k) (by omega)
      have h2 := log_succ_sub_log_le_inv hN
      exact le_trans h1 h2
    have hquad_k : ∀ y ∈ Icc 0 δ_k, autocorr f 0 - autocorr f y ≤ K * y ^ 2 :=
      fun y hy => hquad y ⟨hy.1, le_trans hy.2 hδk_le_inv⟩
    have hcube := integral_autocorr_sub_le_cube_of_quad_collar hf hfc hδk_pos.le hK hquad_k
    have hpow : δ_k ^ 3 ≤ (1 / (N : ℝ)) ^ 3 :=
      pow_le_pow_left₀ hδk_pos.le hδk_le_inv 3
    exact le_trans hcube (mul_le_mul_of_nonneg_left hpow hK)
  have hsum_le :
      (∑ k ∈ Finset.range N,
        ∫ y in (0 : ℝ)..(Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)),
          (autocorr f 0 - autocorr f y)) ≤ K / (N : ℝ) ^ 2 := by
    calc
      (∑ k ∈ Finset.range N,
        ∫ y in (0 : ℝ)..(Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)),
          (autocorr f 0 - autocorr f y)) ≤
          ∑ _k ∈ Finset.range N, K * (1 / (N : ℝ)) ^ 3 :=
        Finset.sum_le_sum hk_le
      _ = (N : ℝ) * (K * (1 / (N : ℝ)) ^ 3) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = K / (N : ℝ) ^ 2 := by
        field_simp [hN_pos.ne']
  calc
    (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (autocorr f x) ^ 2) ≤
        2 * autocorr f 0 * (K / (N : ℝ) ^ 2) :=
      le_trans hbase
        (mul_le_mul_of_nonneg_left hsum_le (mul_nonneg two_pos.le (autocorr_zero_nonneg f)))
    _ = (2 * K / (N : ℝ) ^ 2) * autocorr f 0 := by ring

/-! ## §2. Hyperbolic Polar Weight Energy on the Dyadic Window `[log N, log(2N)]` -/

/-- Exact dyadic window length: `log(2N) - log N = log 2` for `N ≥ 1`. -/
theorem log_two_mul_sub_log_eq (N : ℕ) (hN : 1 ≤ N) :
    Real.log ((2 * N : ℕ) : ℝ) - Real.log (N : ℝ) = Real.log 2 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul two_ne_zero hN_pos.ne']
  ring

/-- On `[log N, log(2N)]` (`N ≥ 1`), `(cosh(x / 2))² ≤ 2 * N`. -/
theorem cosh_half_sq_le_two_mul_nat_on_dyadic_window {N : ℕ} (hN : 1 ≤ N) {x : ℝ}
    (hx : x ∈ Icc (Real.log (N : ℝ)) (Real.log ((2 * N : ℕ) : ℝ))) :
    (Real.cosh (x / 2)) ^ 2 ≤ 2 * (N : ℝ) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have h2N_pos : (0 : ℝ) < ((2 * N : ℕ) : ℝ) := by positivity
  have hx_nonneg : 0 ≤ x :=
    le_trans (Real.log_nonneg (by exact_mod_cast hN)) hx.1
  have hexp_pos : Real.exp (x / 2) ≤ Real.exp (Real.log ((2 * N : ℕ) : ℝ) / 2) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hx.2 two_pos.le)
  have hexp_neg : Real.exp (-x / 2) ≤ Real.exp (Real.log ((2 * N : ℕ) : ℝ) / 2) := by
    refine Real.exp_le_exp.mpr ?_
    have hlog2N_nonneg : 0 ≤ Real.log ((2 * N : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * N))
    linarith
  have hcosh_le : Real.cosh (x / 2) ≤ Real.exp (Real.log ((2 * N : ℕ) : ℝ) / 2) := by
    rw [Real.cosh_eq, show -(x / 2) = -x / 2 by ring]
    linarith
  have hsq_le :
      (Real.cosh (x / 2)) ^ 2 ≤ (Real.exp (Real.log ((2 * N : ℕ) : ℝ) / 2)) ^ 2 :=
    pow_le_pow_left₀ (Real.cosh_pos _).le hcosh_le 2
  have hexp_sq :
      (Real.exp (Real.log ((2 * N : ℕ) : ℝ) / 2)) ^ 2 = 2 * (N : ℝ) := by
    rw [sq, ← Real.exp_add, add_halves, Real.exp_log h2N_pos]
    push_cast; ring
  rwa [hexp_sq] at hsq_le

/-- **Hyperbolic Polar Weight Energy Bound on `[log N, log(2N)]`:**
For every `N ≥ 1`,
`∫ x in log N..log(2N), (cosh(x / 2))² ≤ 2 * N * log 2`. -/
theorem integral_cosh_half_sq_dyadic_window_le {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (Real.cosh (x / 2)) ^ 2) ≤
      2 * (N : ℝ) * Real.log 2 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hle : Real.log (N : ℝ) ≤ Real.log ((2 * N : ℕ) : ℝ) := by
    refine Real.log_le_log hN_pos ?_
    push_cast; linarith
  have hint1 :
      IntervalIntegrable (fun x => (Real.cosh (x / 2)) ^ 2) volume
        (Real.log (N : ℝ)) (Real.log ((2 * N : ℕ) : ℝ)) :=
    ((Real.continuous_cosh.comp (continuous_id.div_const 2)).pow 2).intervalIntegrable _ _
  have hint2 :
      IntervalIntegrable (fun _ : ℝ => 2 * (N : ℝ)) volume
        (Real.log (N : ℝ)) (Real.log ((2 * N : ℕ) : ℝ)) :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hle hint1 hint2
    fun x hx => cosh_half_sq_le_two_mul_nat_on_dyadic_window hN hx
  rw [intervalIntegral.integral_const, log_two_mul_sub_log_eq N hN, smul_eq_mul] at hmono
  linarith

/-! ## §3. Dyadic-Window Polar Tail Decay & Infinite-Grid Closure of Trap 5 -/

/-- **Dyadic-Window Polar Tail Decay Theorem:**
If `f ∈ C²_c(ℝ)` vanishes at the `N` dyadic-window grid nodes `log(N + k)` (`0 ≤ k < N`, `N ≥ 1`)
and satisfies `autocorr f 0 - autocorr f y ≤ K * y²` on `[0, 1 / N]` (`0 ≤ K`), then
`(∫ x in log N..log(2N), |autocorr f x| * cosh(x / 2))² ≤ (4 * log 2 / N) * K * autocorr f 0`. -/
theorem integral_abs_autocorr_mul_cosh_dyadic_window_sq_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {N : ℕ} (hN : 1 ≤ N)
    (hzeros : ∀ k ∈ Finset.range N, autocorr f (Real.log ((N + k : ℕ) : ℝ)) = 0)
    {K : ℝ} (hK : 0 ≤ K)
    (hquad : ∀ y ∈ Icc 0 (1 / (N : ℝ)), autocorr f 0 - autocorr f y ≤ K * y ^ 2) :
    (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ),
        |autocorr f x| * Real.cosh (x / 2)) ^ 2 ≤
      (4 * Real.log 2 / (N : ℝ)) * K * autocorr f 0 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hle : Real.log (N : ℝ) ≤ Real.log ((2 * N : ℕ) : ℝ) := by
    refine Real.log_le_log hN_pos ?_
    push_cast; linarith
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hcs := intervalIntegral_cauchy_schwarz_sq_le hle
    hc.abs.continuousOn
    (Real.continuous_cosh.comp (continuous_id.div_const 2)).continuousOn
  have habs_sq :
      (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), |autocorr f x| ^ 2) =
        ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (autocorr f x) ^ 2 := by
    refine intervalIntegral.integral_congr fun x _ => sq_abs _
  rw [habs_sq] at hcs
  have hL2 := integral_autocorr_sq_dyadic_window_le_of_quad_collar hf hfc hN hzeros hK hquad
  have hcosh := integral_cosh_half_sq_dyadic_window_le hN
  have hL2_nonneg :
      0 ≤ ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (autocorr f x) ^ 2 :=
    intervalIntegral.integral_nonneg hle fun x _ => sq_nonneg _
  have hcosh_nonneg :
      0 ≤ ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (Real.cosh (x / 2)) ^ 2 :=
    intervalIntegral.integral_nonneg hle fun x _ => sq_nonneg _
  have hprod :
      (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (autocorr f x) ^ 2) *
          (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (Real.cosh (x / 2)) ^ 2) ≤
        ((2 * K / (N : ℝ) ^ 2) * autocorr f 0) * (2 * (N : ℝ) * Real.log 2) :=
    mul_le_mul hL2 hcosh hcosh_nonneg
      (mul_nonneg (div_nonneg (mul_nonneg two_pos.le hK) (sq_nonneg _)) (autocorr_zero_nonneg f))
  have hring :
      ((2 * K / (N : ℝ) ^ 2) * autocorr f 0) * (2 * (N : ℝ) * Real.log 2) =
        (4 * Real.log 2 / (N : ℝ)) * K * autocorr f 0 := by
    field_simp [hN_pos.ne']
    ring
  rw [hring] at hprod
  exact le_trans hcs hprod

/-- **Negative Polar Lobe Decay on the Dyadic Window `[log N, log(2N)]`:**
Under the same hypotheses, the negative polar lobe `autocorrNeg f x * cosh(x / 2)` on
`[log N, log(2N)]` satisfies
`(∫ x in log N..log(2N), autocorrNeg f x * cosh(x / 2))² ≤ (4 * log 2 / N) * K * autocorr f 0`. -/
theorem integral_autocorrNeg_mul_cosh_dyadic_window_sq_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {N : ℕ} (hN : 1 ≤ N)
    (hzeros : ∀ k ∈ Finset.range N, autocorr f (Real.log ((N + k : ℕ) : ℝ)) = 0)
    {K : ℝ} (hK : 0 ≤ K)
    (hquad : ∀ y ∈ Icc 0 (1 / (N : ℝ)), autocorr f 0 - autocorr f y ≤ K * y ^ 2) :
    (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ),
        autocorrNeg f x * Real.cosh (x / 2)) ^ 2 ≤
      (4 * Real.log 2 / (N : ℝ)) * K * autocorr f 0 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hle : Real.log (N : ℝ) ≤ Real.log ((2 * N : ℕ) : ℝ) := by
    refine Real.log_le_log hN_pos ?_
    push_cast; linarith
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hc_neg : Continuous (autocorrNeg f) := hc.neg.max continuous_const
  have hint_neg :
      IntervalIntegrable (fun x => autocorrNeg f x * Real.cosh (x / 2)) volume
        (Real.log (N : ℝ)) (Real.log ((2 * N : ℕ) : ℝ)) :=
    (hc_neg.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).intervalIntegrable _ _
  have hint_abs :
      IntervalIntegrable (fun x => |autocorr f x| * Real.cosh (x / 2)) volume
        (Real.log (N : ℝ)) (Real.log ((2 * N : ℕ) : ℝ)) :=
    (hc.abs.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).intervalIntegrable _ _
  have hneg_nonneg :
      0 ≤ ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ),
        autocorrNeg f x * Real.cosh (x / 2) :=
    intervalIntegral.integral_nonneg hle fun x _ =>
      mul_nonneg (autocorrNeg_nonneg f x) (Real.cosh_pos _).le
  have hmono :
      (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ),
          autocorrNeg f x * Real.cosh (x / 2)) ≤
        ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ),
          |autocorr f x| * Real.cosh (x / 2) := by
    refine intervalIntegral.integral_mono_on hle hint_neg hint_abs fun x _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.cosh_pos _).le
    unfold autocorrNeg
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have hsq :
      (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ),
          autocorrNeg f x * Real.cosh (x / 2)) ^ 2 ≤
        (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ),
          |autocorr f x| * Real.cosh (x / 2)) ^ 2 :=
    pow_le_pow_left₀ hneg_nonneg hmono 2
  exact le_trans hsq
    (integral_abs_autocorr_mul_cosh_dyadic_window_sq_le hf hfc hN hzeros hK hquad)

/-- **Infinite-Grid Trap-5 Closure / Kinetic Coercivity Theorem:**
If `f ∈ C²_c(ℝ)` vanishes at the `N` dyadic-window grid nodes `log(N + k)` (`0 ≤ k < N`, `N ≥ 1`),
satisfies `autocorr f 0 - autocorr f y ≤ K * y²` on `[0, 1 / N]` (`0 ≤ K`), and carries negative
polar lobe mass `0 ≤ μ ≤ ∫ x in log N..log(2N), autocorrNeg f x * cosh(x / 2)` in `[log N, log(2N)]`,
then its kinetic / quadratic origin-collar constant `K` must grow at least linearly in `N = e^T`:
`(N : ℝ) * μ² ≤ 4 * log 2 * K * autocorr f 0`. -/
theorem infinite_grid_distant_lobe_kinetic_coercivity {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {N : ℕ} (hN : 1 ≤ N)
    (hzeros : ∀ k ∈ Finset.range N, autocorr f (Real.log ((N + k : ℕ) : ℝ)) = 0)
    {K μ : ℝ} (hK : 0 ≤ K) (hμ : 0 ≤ μ)
    (hquad : ∀ y ∈ Icc 0 (1 / (N : ℝ)), autocorr f 0 - autocorr f y ≤ K * y ^ 2)
    (hlobe : μ ≤ ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ),
      autocorrNeg f x * Real.cosh (x / 2)) :
    (N : ℝ) * μ ^ 2 ≤ 4 * Real.log 2 * K * autocorr f 0 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq :
      μ ^ 2 ≤ (4 * Real.log 2 / (N : ℝ)) * K * autocorr f 0 :=
    le_trans (pow_le_pow_left₀ hμ hlobe 2)
      (integral_autocorrNeg_mul_cosh_dyadic_window_sq_le hf hfc hN hzeros hK hquad)
  have hmul := mul_le_mul_of_nonneg_left hsq hN_pos.le
  have hring :
      (N : ℝ) * ((4 * Real.log 2 / (N : ℝ)) * K * autocorr f 0) =
        4 * Real.log 2 * K * autocorr f 0 := by
    field_simp [hN_pos.ne']
  rwa [hring] at hmul

/-- **Derivative-Free Lévy Tail Bound on `[log N, log(2N)]`:**
Without any quadratic regularity constant `K`, for any `f ∈ C²_c(ℝ)` vanishing at `log(N + k)`
(`0 ≤ k < N`, `N ≥ 1`),
`(∫ x in log N..log(2N), |autocorr f x| * cosh(x / 2))² ≤ 4 * N * log 2 * autocorr f 0 * ∫ y in Ioc 0 (log(N + 1) - log N), (autocorr f 0 - autocorr f y) * archLevySinhWeight y`. -/
theorem integral_abs_autocorr_mul_cosh_dyadic_window_sq_le_levy {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {N : ℕ} (hN : 1 ≤ N)
    (hzeros : ∀ k ∈ Finset.range N, autocorr f (Real.log ((N + k : ℕ) : ℝ)) = 0) :
    (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ),
        |autocorr f x| * Real.cosh (x / 2)) ^ 2 ≤
      4 * (N : ℝ) * Real.log 2 * autocorr f 0 *
        ∫ y in Ioc 0 (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)),
          (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hle : Real.log (N : ℝ) ≤ Real.log ((2 * N : ℕ) : ℝ) := by
    refine Real.log_le_log hN_pos ?_
    push_cast; linarith
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hcs := intervalIntegral_cauchy_schwarz_sq_le hle
    hc.abs.continuousOn
    (Real.continuous_cosh.comp (continuous_id.div_const 2)).continuousOn
  have habs_sq :
      (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), |autocorr f x| ^ 2) =
        ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (autocorr f x) ^ 2 :=
    intervalIntegral.integral_congr fun x _ => sq_abs _
  rw [habs_sq] at hcs
  have hL2 := integral_autocorr_sq_dyadic_window_le_levy_collar hf hfc hN hzeros
  have hcosh := integral_cosh_half_sq_dyadic_window_le hN
  have hcosh_nonneg :
      0 ≤ ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (Real.cosh (x / 2)) ^ 2 :=
    intervalIntegral.integral_nonneg hle fun x _ => sq_nonneg _
  have hlevy_nonneg :
      0 ≤ ∫ y in Ioc 0 (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)),
        (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
    refine setIntegral_nonneg measurableSet_Ioc fun y hy => ?_
    exact mul_nonneg (autocorr_sub_nonneg hfc hf.continuous y) (archLevySinhWeight_pos hy.1).le
  have hprod :
      (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (autocorr f x) ^ 2) *
          (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (Real.cosh (x / 2)) ^ 2) ≤
        (2 * autocorr f 0 *
          ∫ y in Ioc 0 (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)),
            (autocorr f 0 - autocorr f y) * archLevySinhWeight y) *
          (2 * (N : ℝ) * Real.log 2) :=
    mul_le_mul hL2 hcosh hcosh_nonneg
      (mul_nonneg (mul_nonneg two_pos.le (autocorr_zero_nonneg f)) hlevy_nonneg)
  calc
    (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ),
        |autocorr f x| * Real.cosh (x / 2)) ^ 2 ≤
        (2 * autocorr f 0 *
          ∫ y in Ioc 0 (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)),
            (autocorr f 0 - autocorr f y) * archLevySinhWeight y) *
          (2 * (N : ℝ) * Real.log 2) := le_trans hcs hprod
    _ = 4 * (N : ℝ) * Real.log 2 * autocorr f 0 *
          ∫ y in Ioc 0 (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)),
            (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by ring

end

end GaloisForLFunctions.BiScaleUncertainty
