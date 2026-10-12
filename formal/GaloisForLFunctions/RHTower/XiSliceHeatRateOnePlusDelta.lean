import GaloisForLFunctions.RHTower.XiSliceEulerDerivativeLowerBound
import GaloisForLFunctions.RHTower.XiSliceHeatGaussianDerivativeRepresentation
import GaloisForLFunctions.RHTower.XiSliceEulerGrowthAndMonotonicity
import GaloisForLFunctions.RHTower.XiSliceStripGrowthBounds
import GaloisForLFunctions.RHTower.XiSliceHeatEffectiveKKL

/-!
# Heat `(1+δ)/log t` makes every heated slice coefficient positive

**Theorem** (`exists_xiSliceHeatTransfer_pos_heat_one_add_over_log`).  For every `δ ∈ (0, 1]` there
is `t₀` such that for `|t| ≥ t₀`, every heat `λ ≥ (1+δ)/log |t|` and every `m`,

  `T_{2m}(λ, 0, t) > 0`.

This lowers the constant of the effective slice Ki–Kim–Lee theorem
(`exists_xiSliceHeatTransfer_pos_heat_over_log`, heat `100/log t`) to `1 + δ`.

Proof.  Orders `2m ≥ log t`, `m = 0`, larger heats and negative heights are handled as in the
heat-`100/log t` theorem.  For `1 ≤ N = 2m ≤ log t` and `λ = κ/log t`, `κ = 1 + δ`, use the
Gaussian-derivative representation `√(2π) T_N = ∫ e^{−w²/2} S^{(N)}(√λ w)/N! dw`
(`xiSliceHeatTransfer_eq_integral_iteratedDeriv`), with `x = √λ w`:

* for `|x| ≥ ½` the integrand is `≥ 0`, since every derivative of the slice is `≥ 0` on `[½, ∞)` and
  `S^{(N)}` is even for even `N`;
* on the window `x ∈ [1 + δ/2, 1 + δ]` the lower bound at Euler points
  (`exists_iteratedDeriv_xiSliceProduct_ge_euler`) and the growth of `S` give the integrand
  `≥ S(½+δ/4) t^{δ/4 − δ²/8} e^{−O(1)} · L′ᴺ/N! · (log t)^{−1/2}`, because
  `x − ½ − δ/4 − x²/(2κ) ≥ δ/4 − δ²/8` there;
* for `|x| < ½` the Cauchy estimate on the circle of radius `N/(log t + 2C)` and the strip bound
  `|S| ≤ C S(½+δ/4) t^{−δ/8}` (`exists_norm_xiSliceProduct_le_strip`) give
  `|S^{(N)}(x)|/N! ≤ C S(½+δ/4) t^{−δ/8} eᴺ ((log t + 2C)/N)ᴺ`.

With `N! ≤ e√N (N/e)ᴺ` the window wins by `t^{3δ/8 − δ²/8}/log t`.
-/

open Complex MeasureTheory Filter Topology Metric
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-- The Gaussian-derivative integrand is integrable. -/
theorem integrable_gauss_mul_iteratedDeriv_xiSliceProduct {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ)
    (n : ℕ) :
    Integrable (fun w : ℝ => ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
      * (iteratedDeriv n (xiSliceProduct t) ((Real.sqrt lam * w : ℝ) : ℂ) / n.factorial)) := by
  have h := (integrable_gaussKernelMoment hlam t n).integral_prod_left
  refine h.congr (Eventually.of_forall fun w => ?_)
  have hk : kernelSliceMoment riemannKernelReal (Real.sqrt lam * w) t n
      = iteratedDeriv n (xiSliceProduct t) ((Real.sqrt lam * w : ℝ) : ℂ) / n.factorial := by
    rw [kernelSliceMoment_eq_iteratedDeriv riemannKernel_superExp, cosTransform_riemannKernel_slice]
  simp only [Function.uncurry_apply_pair]
  rw [integral_const_mul, ← hk]
  rfl

/-- **Integral lower bound from a window.**  If `h ≥ P` on `[a, b]`, `h ≥ −B` on `(−c, c)` and
`h ≥ 0` off `(−c, c)`, with `0 ≤ c ≤ a ≤ b`, then `∫ h ≥ (b − a) P − 2c B`. -/
theorem integral_ge_of_window {h : ℝ → ℝ} (hint : Integrable h) {a b c P B : ℝ} (hab : a ≤ b)
    (hc : 0 ≤ c) (hca : c ≤ a) (h1 : ∀ w ∈ Set.Icc a b, P ≤ h w)
    (h0 : ∀ w ∈ Set.Ioo (-c) c, -B ≤ h w) (hout : ∀ w, w ∉ Set.Ioo (-c) c → 0 ≤ h w) :
    (b - a) * P - 2 * c * B ≤ ∫ w, h w := by
  set φ : ℝ → ℝ := fun w => (Set.Icc a b).indicator (fun _ => P) w
    - (Set.Ioo (-c) c).indicator (fun _ => B) w with hφ
  have hI1 : Integrable ((Set.Icc a b).indicator (fun _ : ℝ => P)) :=
    (integrableOn_const (by simp [Real.volume_Icc])).integrable_indicator measurableSet_Icc
  have hI0 : Integrable ((Set.Ioo (-c) c).indicator (fun _ : ℝ => B)) :=
    (integrableOn_const (by simp [Real.volume_Ioo])).integrable_indicator measurableSet_Ioo
  have hφint : Integrable φ := hI1.sub hI0
  have hle : φ ≤ h := by
    intro w
    simp only [hφ]
    by_cases hw0 : w ∈ Set.Ioo (-c) c
    · have hw1 : w ∉ Set.Icc a b := fun hw => by linarith [hw0.2, hw.1]
      rw [Set.indicator_of_notMem hw1, Set.indicator_of_mem hw0]
      linarith [h0 w hw0]
    · rw [Set.indicator_of_notMem hw0, sub_zero]
      by_cases hw1 : w ∈ Set.Icc a b
      · rw [Set.indicator_of_mem hw1]; exact h1 w hw1
      · rw [Set.indicator_of_notMem hw1]; exact hout w hw0
  have hmono := integral_mono hφint hint hle
  have hφval : ∫ w, φ w = (b - a) * P - 2 * c * B := by
    simp only [hφ]
    rw [integral_sub hI1 hI0, integral_indicator_const _ measurableSet_Icc,
      integral_indicator_const _ measurableSet_Ioo, Real.volume_real_Icc_of_le hab,
      Real.volume_real_Ioo_of_le (by linarith), smul_eq_mul, smul_eq_mul]
    ring
  linarith

/-- Even-order derivatives of the slice are even. -/
theorem iteratedDeriv_xiSliceProduct_neg_even (t : ℝ) (m : ℕ) (z : ℂ) :
    iteratedDeriv (2 * m) (xiSliceProduct t) (-z) = iteratedDeriv (2 * m) (xiSliceProduct t) z := by
  have h := iteratedDeriv_comp_neg (2 * m) (xiSliceProduct t) z
  have hf : (fun x => xiSliceProduct t (-x)) = xiSliceProduct t := funext (xiSliceProduct_neg t)
  rw [hf, pow_mul, neg_one_sq, one_pow, one_smul] at h
  exact h.symm

/-- Even-order derivatives of the slice have nonnegative real part on `|x| ≥ ½`. -/
theorem re_iteratedDeriv_xiSliceProduct_even_nonneg (t : ℝ) (m : ℕ) {x : ℝ} (hx : 1 / 2 ≤ |x|) :
    0 ≤ (iteratedDeriv (2 * m) (xiSliceProduct t) (x : ℂ)).re := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h] at hx
    exact (Complex.nonneg_iff.mp (iteratedDeriv_xiSliceProduct_nonneg_of_half_le t hx (2 * m))).1
  · rw [abs_of_nonpos h] at hx
    rw [← iteratedDeriv_xiSliceProduct_neg_even, ← Complex.ofReal_neg]
    exact (Complex.nonneg_iff.mp (iteratedDeriv_xiSliceProduct_nonneg_of_half_le t hx (2 * m))).1

/-- **Inner Cauchy bound.**  For `|x| < ½` and `1 ≤ N ≤ log t`, on the circle of radius
`N/(log t + 2C_η)` the slice is at most `C S(½+2η) t^{−η} eᴺ`, so
`|S^{(N)}(x)|/N! ≤ C S(½+2η) e^{N − η log t} ((log t + 2C_η)/N)ᴺ`. -/
theorem exists_norm_iteratedDeriv_xiSliceProduct_le_inner {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 80 ≤ t → ∀ x : ℝ, |x| < 1 / 2 → ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) ≤ Real.log t →
      ‖iteratedDeriv N (xiSliceProduct t) (x : ℂ)‖ / N.factorial ≤
        C * xiSliceReal t (1 / 2 + 2 * η) * (Real.exp (N - η * Real.log t)
          * ((Real.log t + 2 * xiEulerConstant η) / N) ^ N) := by
  obtain ⟨C, hC, hS⟩ := exists_norm_xiSliceProduct_le_strip (R₁ := 2) hη hη1 (by norm_num)
  refine ⟨C, hC, fun t ht x hx N hN1 hNu => ?_⟩
  have ht0 : 0 < t := by linarith
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  rw [← hudef] at hNu ⊢
  rw [← hEdef]
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hu0 : 0 < u := by linarith
  have hu2E : 0 < u + 2 * E := by linarith
  set S₀ := xiSliceReal t (1 / 2 + 2 * η) with hS₀
  have hS₀0 : 0 ≤ S₀ := xiSliceReal_nonneg t _
  obtain ⟨r, hrdef⟩ : ∃ r, r = N / (u + 2 * E) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hu2E]; linarith
  have hrN : (u + 2 * E) * r = N := by rw [hrdef]; field_simp
  set M := C * S₀ * Real.exp ((u + 2 * E) * r - η * u) with hM
  have hMb : ∀ z ∈ sphere (x : ℂ) r, ‖xiSliceProduct t z‖ ≤ M := by
    intro z hz
    have hzr : ‖z - x‖ = r := mem_sphere_iff_norm.mp hz
    have hza : |z.re - x| ≤ r := by
      have := Complex.abs_re_le_norm (z - x)
      rw [Complex.sub_re, Complex.ofReal_re] at this
      linarith
    have hzc : |z.im| ≤ r := by
      have := Complex.abs_im_le_norm (z - x)
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      linarith
    have hz' : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
    have habs : |z.re| < 1 / 2 + r := by
      have := abs_add_le (z.re - x) x
      rw [sub_add_cancel] at this
      linarith
    obtain ⟨hin, hout⟩ := hS t z.re z.im (by linarith) (by linarith)
    rw [hz']
    have hbase : C * S₀ * Real.exp (-(η * u)) ≤ M := by
      rw [hM]
      gcongr
      have := mul_nonneg hu2E.le hr0.le
      linarith
    by_cases ha : |z.re| < 1 / 2 + η
    · refine le_trans (hin ha) (le_of_eq_of_le ?_ hbase)
      rw [Real.rpow_def_of_pos ht0, ← hudef, ← hS₀]
      ring_nf
    · push Not at ha
      refine le_trans (hout ha (by linarith)) ?_
      set y := max |z.re| (1 / 2 + 2 * η) with hy
      have hy1 : 1 / 2 + 2 * η ≤ y := le_max_right _ _
      have hy2 : y ≤ t / 2 := max_le (by linarith) (by linarith)
      have hgrow := (xiSliceReal_growth_euler (t := t) hη (by linarith) (y₁ := 1 / 2 + 2 * η)
        (y₂ := y) (by linarith) hy1 hy2).2
      rw [← hudef, ← hEdef] at hgrow
      have hexp : (u + 2 * E) * (y - (1 / 2 + 2 * η)) ≤ (u + 2 * E) * r - η * u := by
        rcases le_total |z.re| (1 / 2 + 2 * η) with h | h
        · rw [hy, max_eq_right h, sub_self, mul_zero]
          have h1 : η ≤ r := by linarith
          have h2 := mul_le_mul_of_nonneg_left h1 hu0.le
          have h3 := mul_nonneg hE0.le hr0.le
          linarith
        · rw [hy, max_eq_left h]
          have h1 : |z.re| - (1 / 2 + 2 * η) ≤ r - 2 * η := by linarith
          have h2 := mul_le_mul_of_nonneg_left h1 hu2E.le
          have h3 := mul_nonneg hE0.le hη.le
          nlinarith
      calc C * xiSliceReal t y
          ≤ C * (S₀ * Real.exp ((u + 2 * E) * (y - (1 / 2 + 2 * η)))) :=
            mul_le_mul_of_nonneg_left hgrow hC.le
        _ ≤ C * (S₀ * Real.exp ((u + 2 * E) * r - η * u)) := by gcongr
        _ = M := by rw [hM]; ring
  have hcauchy := norm_iteratedDeriv_xiSliceProduct_le t N hr0 hMb
  have hfact : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [div_le_iff₀ hfact]
  calc ‖iteratedDeriv N (xiSliceProduct t) (x : ℂ)‖ ≤ N.factorial * M / r ^ N := hcauchy
    _ = C * S₀ * (Real.exp (N - η * u) * ((u + 2 * E) / N) ^ N) * N.factorial := by
        rw [hM, hrN, hrdef, div_pow, div_pow]
        field_simp

/-- **Weighted window bound.**  For `x ∈ [1+δ/2, 1+δ]`, `κ = 1+δ` and `u = log t`,
`S(x) e^{−x²u/(2κ)} ≥ S(½+δ/4) e^{u(δ/4 − δ²/8) − 2(log 2 + 2C_{δ/8})}`. -/
theorem xiSliceReal_mul_gauss_ge_window {δ t x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : 8 ≤ t)
    (hx1 : 1 + δ / 2 ≤ x) (hx2 : x ≤ 1 + δ) (hxt : x ≤ t / 2) :
    xiSliceReal t (1 / 2 + δ / 4) * Real.exp (Real.log t * (δ / 4 - δ ^ 2 / 8)
        - 2 * (Real.log 2 + 2 * xiEulerConstant (δ / 8)))
      ≤ xiSliceReal t x * Real.exp (-(x ^ 2 * Real.log t / (2 * (1 + δ)))) := by
  have ht0 : 0 < t := by linarith
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant (δ / 8) := ⟨_, rfl⟩
  rw [← hudef, ← hEdef]
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos (by positivity)
  have hu0 : 0 ≤ u := by rw [hudef]; exact Real.log_nonneg (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgrow := (xiSliceReal_growth_euler (t := t) (η := δ / 8) (by positivity) ht
    (y₁ := 1 / 2 + δ / 4) (y₂ := x) (by linarith) (by linarith) hxt).1
  rw [Real.log_div ht0.ne' (by norm_num), ← hudef, ← hEdef] at hgrow
  have hQ : δ / 4 - δ ^ 2 / 8 ≤ x - (1 / 2 + δ / 4) - x ^ 2 / (2 * (1 + δ)) := by
    have hk : 0 < 2 * (1 + δ) := by positivity
    have h1 : 0 ≤ 1 + δ - x := by linarith
    have h2 : 1 + δ - x ≤ δ / 2 := by linarith
    have h3 : (1 + δ - x) ^ 2 ≤ (δ / 2) ^ 2 := pow_le_pow_left₀ h1 h2 2
    have h4 : x ^ 2 / (2 * (1 + δ)) ≤ x - 1 / 2 - δ / 2 + δ ^ 2 / 8 := by
      rw [div_le_iff₀ hk]
      nlinarith [pow_pos hδ 3]
    linarith
  have hexp : u * (δ / 4 - δ ^ 2 / 8) - 2 * (Real.log 2 + 2 * E)
      ≤ (u - Real.log 2 - 2 * E) * (x - (1 / 2 + δ / 4)) - x ^ 2 * u / (2 * (1 + δ)) := by
    have h1 := mul_le_mul_of_nonneg_left hQ hu0
    have h2 : x - (1 / 2 + δ / 4) ≤ 2 := by linarith
    have h3 : 0 ≤ x - (1 / 2 + δ / 4) := by linarith
    have hc : 0 ≤ Real.log 2 + 2 * E := by linarith
    have h4 := mul_le_mul_of_nonneg_left h2 hc
    have e : x ^ 2 * u / (2 * (1 + δ)) = u * (x ^ 2 / (2 * (1 + δ))) := by ring
    rw [e]
    nlinarith
  have hS := xiSliceReal_nonneg t (1 / 2 + δ / 4)
  calc xiSliceReal t (1 / 2 + δ / 4) * Real.exp (u * (δ / 4 - δ ^ 2 / 8) - 2 * (Real.log 2 + 2 * E))
      ≤ xiSliceReal t (1 / 2 + δ / 4) * Real.exp ((u - Real.log 2 - 2 * E) * (x - (1 / 2 + δ / 4))
          - x ^ 2 * u / (2 * (1 + δ))) := by gcongr
    _ = xiSliceReal t (1 / 2 + δ / 4) * Real.exp ((u - Real.log 2 - 2 * E) * (x - (1 / 2 + δ / 4)))
          * Real.exp (-(x ^ 2 * u / (2 * (1 + δ)))) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ xiSliceReal t x * Real.exp (-(x ^ 2 * u / (2 * (1 + δ)))) := by gcongr

/-- **The window beats the inner region.**  The numerical comparison behind the low orders:
with `L′ = u − log 2 − 2C₈`, `1 ≤ N ≤ u` and `u e^{−δu/4}` small,
`2C e^{N − δu/8} ((u + 2C_E)/N)ᴺ < δ e^{u(δ/4 − δ²/8) − 2(log 2 + 2C_E)} L′ᴺ/N! /(40π√(2u))`. -/
theorem heat_window_comparison {δ C E E₈ u : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 < C)
    (hE : 0 ≤ E) (hE₈ : 0 ≤ E₈) (hu : 0 < u) (hu2 : 2 * (Real.log 2 + 2 * E₈) ≤ u)
    (hK : u * (80 * Real.pi * Real.sqrt 2 * C
        * Real.exp (2 * (2 * E + Real.log 2 + 2 * E₈) + (2 * (Real.log 2 + 2 * E) + 1)) / δ)
      < Real.exp (δ / 4 * u))
    {N : ℕ} (hN1 : 1 ≤ N) (hNu : (N : ℝ) ≤ u) :
    2 * (C * (Real.exp (N - δ / 8 * u) * ((u + 2 * E) / N) ^ N)) <
      δ * (Real.exp (u * (δ / 4 - δ ^ 2 / 8) - 2 * (Real.log 2 + 2 * E))
        * ((u - Real.log 2 - 2 * E₈) ^ N / N.factorial
          * (1 / (40 * Real.pi * Real.sqrt (2 * u))))) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨L', hL'⟩ : ∃ L', L' = u - Real.log 2 - 2 * E₈ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Real.log 2 + 2 * E := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = 2 * E + Real.log 2 + 2 * E₈ := ⟨_, rfl⟩
  rw [← hL', ← hc]
  rw [← hc, ← hc'] at hK
  have hL'2 : u / 2 ≤ L' := by rw [hL']; linarith
  have hL'0 : 0 < L' := by linarith
  have hc'0 : 0 ≤ c' := by rw [hc']; linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpi := Real.pi_pos
  -- `(u + 2E)ᴺ ≤ e^{2c'} L′ᴺ`
  have hρ : (u + 2 * E) ^ N ≤ Real.exp (2 * c') * L' ^ N := by
    have hsum : u + 2 * E = L' * (1 + c' / L') := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hL'0.ne', hL', hc']; ring
    have h1 : (1 + c' / L') ^ N ≤ Real.exp (2 * c') := by
      calc (1 + c' / L') ^ N ≤ Real.exp (c' / L') ^ N :=
            pow_le_pow_left₀ (by have := div_nonneg hc'0 hL'0.le; linarith)
              (by linarith [Real.add_one_le_exp (c' / L')]) N
        _ = Real.exp (N * (c' / L')) := by rw [Real.exp_nat_mul]
        _ ≤ Real.exp (2 * c') := by
            refine Real.exp_le_exp.mpr ?_
            rw [← mul_div_assoc, div_le_iff₀ hL'0]
            have := mul_le_mul_of_nonneg_right (by linarith : (N : ℝ) ≤ 2 * L') hc'0
            linarith
    rw [hsum, mul_pow, mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_left h1 (pow_pos hL'0 N).le
  -- the common factor `W = L′ᴺ/(N/e)ᴺ`
  obtain ⟨W, hW⟩ : ∃ W, W = L' ^ N / ((N : ℝ) / Real.exp 1) ^ N := ⟨_, rfl⟩
  have hNe : 0 < ((N : ℝ) / Real.exp 1) ^ N := pow_pos (div_pos hN0 (Real.exp_pos 1)) N
  have hW0 : 0 < W := by rw [hW]; exact div_pos (pow_pos hL'0 N) hNe
  obtain ⟨eA, heA⟩ : ∃ eA, eA = Real.exp (δ / 8 * u) := ⟨_, rfl⟩
  obtain ⟨eB, heB⟩ : ∃ eB, eB = Real.exp (u * (δ / 4 - δ ^ 2 / 8)) := ⟨_, rfl⟩
  obtain ⟨e1, he1⟩ : ∃ e1, e1 = Real.exp (2 * c') := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ e2, e2 = Real.exp (2 * c + 1) := ⟨_, rfl⟩
  have heA0 : 0 < eA := heA ▸ Real.exp_pos _
  have heB0 : 0 < eB := heB ▸ Real.exp_pos _
  have he10 : 0 < e1 := he1 ▸ Real.exp_pos _
  have he20 : 0 < e2 := he2 ▸ Real.exp_pos _
  -- the left side
  have hX : Real.exp (N - δ / 8 * u) * ((u + 2 * E) / N) ^ N ≤ e1 * W / eA := by
    have e : Real.exp (N - δ / 8 * u) * ((u + 2 * E) / N) ^ N
        = (u + 2 * E) ^ N / ((N : ℝ) / Real.exp 1) ^ N / eA := by
      rw [heA, Real.exp_sub, div_pow, div_pow, ← Real.exp_nat_mul, mul_one]
      field_simp
    rw [e, hW, he1]
    apply div_le_div_of_nonneg_right _ heA0.le
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hNe]
    exact hρ
  -- the right side
  have hfact := RHTower.factorial_le_exp_one_mul_sqrt_mul_pow hN1
  have hfact0 : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hsN : Real.sqrt N ≤ Real.sqrt u := Real.sqrt_le_sqrt hNu
  have hsN0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hs2u : Real.sqrt (2 * u) = Real.sqrt 2 * Real.sqrt u := Real.sqrt_mul (by norm_num) u
  have hsuu : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
  have hY : Real.exp (u * (δ / 4 - δ ^ 2 / 8) - 2 * c) = Real.exp 1 * (eB / e2) := by
    rw [heB, he2, ← Real.exp_sub, ← Real.exp_add]; ring_nf
  have hR : W / (40 * Real.pi * Real.sqrt 2 * Real.exp 1 * u)
      ≤ L' ^ N / N.factorial * (1 / (40 * Real.pi * Real.sqrt (2 * u))) := by
    have h1 : L' ^ N / (Real.exp 1 * Real.sqrt N * ((N : ℝ) / Real.exp 1) ^ N)
        ≤ L' ^ N / N.factorial := div_le_div_of_nonneg_left (pow_pos hL'0 N).le hfact0 hfact
    have h2 : W / (40 * Real.pi * Real.sqrt 2 * Real.exp 1 * u)
        ≤ L' ^ N / (Real.exp 1 * Real.sqrt N * ((N : ℝ) / Real.exp 1) ^ N)
          * (1 / (40 * Real.pi * Real.sqrt (2 * u))) := by
      have hden : Real.sqrt N * Real.sqrt u ≤ u :=
        le_of_le_of_eq (mul_le_mul_of_nonneg_right hsN (Real.sqrt_nonneg u)) hsuu
      rw [hW, hs2u, div_div, div_mul_div_comm, mul_one]
      apply div_le_div_of_nonneg_left (pow_pos hL'0 N).le
        (mul_pos (mul_pos (mul_pos (Real.exp_pos 1) hsN0) hNe)
          (mul_pos (by positivity) (mul_pos (Real.sqrt_pos.mpr (by norm_num))
            (Real.sqrt_pos.mpr hu))))
      calc Real.exp 1 * Real.sqrt N * ((N : ℝ) / Real.exp 1) ^ N
            * (40 * Real.pi * (Real.sqrt 2 * Real.sqrt u))
          = 40 * Real.pi * Real.sqrt 2 * Real.exp 1 * (Real.sqrt N * Real.sqrt u)
            * ((N : ℝ) / Real.exp 1) ^ N := by ring
        _ ≤ 40 * Real.pi * Real.sqrt 2 * Real.exp 1 * u * ((N : ℝ) / Real.exp 1) ^ N := by
            gcongr
        _ = ((N : ℝ) / Real.exp 1) ^ N * (40 * Real.pi * Real.sqrt 2 * Real.exp 1 * u) := by ring
    exact le_trans h2 (mul_le_mul_of_nonneg_right h1 (by positivity))
  -- the core comparison
  have hK' : u * (80 * Real.pi * Real.sqrt 2 * C * (e1 * e2) / δ) < eA * eB := by
    have e : Real.exp (2 * c' + (2 * c + 1)) = e1 * e2 := by rw [he1, he2, Real.exp_add]
    rw [← e]
    calc _ < Real.exp (δ / 4 * u) := hK
      _ ≤ eA * eB := by
          rw [heA, heB, ← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          have := mul_nonneg (mul_nonneg hδ.le hu.le) (by linarith : (0 : ℝ) ≤ 1 - δ)
          nlinarith
  have hcore : 2 * C * e1 / eA < δ * (eB / e2) / (40 * Real.pi * Real.sqrt 2 * u) := by
    have hd : 0 < 40 * Real.pi * Real.sqrt 2 * u :=
      mul_pos (mul_pos (by positivity) (Real.sqrt_pos.mpr (by norm_num))) hu
    rw [div_lt_div_iff₀ heA0 hd]
    calc 2 * C * e1 * (40 * Real.pi * Real.sqrt 2 * u)
        = δ / e2 * (u * (80 * Real.pi * Real.sqrt 2 * C * (e1 * e2) / δ)) := by
          field_simp; ring
      _ < δ / e2 * (eA * eB) := mul_lt_mul_of_pos_left hK' (div_pos hδ he20)
      _ = δ * (eB / e2) * eA := by ring
  rw [hY]
  calc 2 * (C * (Real.exp (N - δ / 8 * u) * ((u + 2 * E) / N) ^ N))
      ≤ 2 * (C * (e1 * W / eA)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX hC.le) (by norm_num)
    _ = 2 * C * e1 / eA * W := by ring
    _ < δ * (eB / e2) / (40 * Real.pi * Real.sqrt 2 * u) * W :=
        mul_lt_mul_of_pos_right hcore hW0
    _ = δ * (Real.exp 1 * (eB / e2)) * (W / (40 * Real.pi * Real.sqrt 2 * Real.exp 1 * u)) := by
        field_simp
    _ ≤ δ * (Real.exp 1 * (eB / e2)) * (L' ^ N / N.factorial
          * (1 / (40 * Real.pi * Real.sqrt (2 * u)))) :=
        mul_le_mul_of_nonneg_left hR
          (mul_pos hδ (mul_pos (Real.exp_pos 1) (div_pos heB0 he20))).le
    _ = _ := by ring

/-- **Low orders at heat `(1+δ)/log t`.**  For `1 ≤ m` and `2m ≤ log t`, `T_{2m}((1+δ)/log t, 0, t)`
is positive once `t` is large. -/
theorem exists_xiSliceHeatTransfer_pos_low_order {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ m : ℕ, 1 ≤ m → (2 * m : ℝ) ≤ Real.log t →
      0 < xiSliceHeatTransfer ((1 + δ) / Real.log t) 0 t (2 * m) := by
  obtain ⟨C, hC, hinner⟩ :=
    exists_norm_iteratedDeriv_xiSliceProduct_le_inner (η := δ / 8) (by positivity) (by linarith)
  obtain ⟨t₄, -, hM4⟩ := RHTower.exists_iteratedDeriv_xiSliceProduct_ge_euler
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant (δ / 8) := ⟨_, rfl⟩
  obtain ⟨E₈, hE₈def⟩ : ∃ E₈, E₈ = xiEulerConstant (1 / 8) := ⟨_, rfl⟩
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos (by positivity)
  have hE₈0 : 0 < E₈ := hE₈def ▸ xiEulerConstant_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨K, hKdef⟩ : ∃ K, K = 80 * Real.pi * Real.sqrt 2 * C
      * Real.exp (2 * (2 * E + Real.log 2 + 2 * E₈) + (2 * (Real.log 2 + 2 * E) + 1)) / δ :=
    ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; positivity
  have e5 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (δ / 4)
    (by positivity))).2 (1 / K) (by positivity)
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.mp e5
  obtain ⟨L₀, hL₀⟩ : ∃ L₀, L₀ = max (max (Real.log 80) (Real.log t₄))
      (max (2 * (Real.log 2 + 2 * E₈)) (max U 1)) := ⟨_, rfl⟩
  refine ⟨max 80 (max t₄ (Real.exp L₀)), le_max_left _ _, ?_⟩
  intro t ht m hm1 hmu
  have ht80 : 80 ≤ t := le_trans (le_max_left _ _) ht
  have ht4 : t₄ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htL : Real.exp L₀ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht0 : 0 < t := by linarith
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  have hLu : L₀ ≤ u := by
    rw [hudef, ← Real.log_exp L₀]; exact Real.log_le_log (Real.exp_pos _) htL
  rw [hL₀] at hLu
  have hu2 : 2 * (Real.log 2 + 2 * E₈) ≤ u :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLu
  have huU : U ≤ u :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hLu
  have hu1 : 1 ≤ u :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hLu
  have hu0 : 0 < u := by linarith
  have hKu : u * K < Real.exp (δ / 4 * u) := by
    have h := hU u huU
    rw [Real.rpow_one, show -(δ / 4) * u = -(δ / 4 * u) by ring, Real.exp_neg] at h
    have hx := Real.exp_pos (δ / 4 * u)
    rw [lt_div_iff₀ hK0] at h
    calc u * K = u * (Real.exp (δ / 4 * u))⁻¹ * K * Real.exp (δ / 4 * u) := by field_simp
      _ < 1 * Real.exp (δ / 4 * u) := mul_lt_mul_of_pos_right h hx
      _ = Real.exp (δ / 4 * u) := one_mul _
  -- the order and the heat
  obtain ⟨N, hNdef⟩ : ∃ N, N = 2 * m := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by omega
  have hNu : (N : ℝ) ≤ u := by rw [hNdef, hudef]; push_cast; exact hmu
  rw [← hudef]
  obtain ⟨lam, hlamdef⟩ : ∃ lam, lam = (1 + δ) / u := ⟨_, rfl⟩
  rw [← hlamdef, ← hNdef]
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt lam := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hlam0
  have hs2 : s ^ 2 = lam := by rw [hsdef]; exact Real.sq_sqrt hlam0.le
  -- the representation and its real part
  have hrep := xiSliceHeatTransfer_eq_integral_iteratedDeriv hlam0.le t N
  have hint := integrable_gauss_mul_iteratedDeriv_xiSliceProduct hlam0.le t N
  rw [← hsdef] at hrep hint
  set F : ℝ → ℂ := fun w => ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
    * (iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ) / N.factorial) with hF
  have hre : ∫ w, (F w).re = (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
      * xiSliceHeatTransfer lam 0 t N).re := by
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [hrep]; exact this
  have hfact0 : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hFre : ∀ w, (F w).re = Real.exp (-(w ^ 2 / 2))
      * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial) := by
    intro w
    simp only [hF]
    rw [Complex.re_ofReal_mul, Complex.div_natCast_re]
  -- constants of the window argument
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, S₀ = xiSliceReal t (1 / 2 + δ / 4) := ⟨_, rfl⟩
  have hS₀0 : 0 < S₀ := by rw [hS₀]; exact xiSliceReal_pos t (by linarith)
  have hlogt2 : Real.log (t / 2) = u - Real.log 2 := by
    rw [Real.log_div ht0.ne' (by norm_num), hudef]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (u - Real.log 2 - 2 * E₈) ^ N / N.factorial
      * (1 / (40 * Real.pi * Real.sqrt (2 * u))) := ⟨_, rfl⟩
  have hL'0 : 0 < u - Real.log 2 - 2 * E₈ := by linarith
  have hQ0 : 0 ≤ Q := by
    rw [hQ]; exact mul_nonneg (div_nonneg (pow_pos hL'0 N).le hfact0.le) (by positivity)
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, P₀ = S₀ * Real.exp (u * (δ / 4 - δ ^ 2 / 8)
      - 2 * (Real.log 2 + 2 * E)) * Q := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = C * S₀ * (Real.exp (N - δ / 8 * u)
      * ((u + 2 * E) / N) ^ N) := ⟨_, rfl⟩
  have hwin := integral_ge_of_window (h := fun w => (F w).re) hint.re
    (a := (1 + δ / 2) / s) (b := (1 + δ) / s) (c := 1 / 2 / s) (P := P₀) (B := B₀)
    (div_le_div_of_nonneg_right (by linarith) hs0.le) (by positivity)
    (div_le_div_of_nonneg_right (by linarith) hs0.le) ?_ ?_ ?_
  rotate_left
  · -- the window
    intro w hw
    have hx1 : 1 + δ / 2 ≤ s * w := by
      have := hw.1; rw [div_le_iff₀ hs0] at this; linarith
    have hx2 : s * w ≤ 1 + δ := by
      have := hw.2; rw [le_div_iff₀ hs0] at this; linarith
    have hM := hM4 t ht4 (s * w) (by linarith) (by linarith) N hN1 (by rw [← hudef]; exact hNu)
    rw [← div_eq_inv_mul, Complex.div_natCast_re, hlogt2, ← hE₈def, ← hudef] at hM
    have hF' := xiSliceReal_mul_gauss_ge_window (t := t) hδ hδ1 (by linarith) hx1 hx2
      (by linarith)
    rw [← hudef, ← hEdef, ← hS₀] at hF'
    have hg : Real.exp (-(w ^ 2 / 2)) = Real.exp (-((s * w) ^ 2 * u / (2 * (1 + δ)))) := by
      congr 2
      rw [mul_pow, hs2, hlamdef]
      field_simp
    rw [hFre, hg, hP₀]
    have hQ' : Q = (u - Real.log 2 - 2 * E₈) ^ N / N.factorial
        * (1 / (40 * Real.pi * Real.sqrt (2 * u))) := hQ
    calc S₀ * Real.exp (u * (δ / 4 - δ ^ 2 / 8) - 2 * (Real.log 2 + 2 * E)) * Q
        ≤ xiSliceReal t (s * w) * Real.exp (-((s * w) ^ 2 * u / (2 * (1 + δ)))) * Q :=
          mul_le_mul_of_nonneg_right hF' hQ0
      _ = Real.exp (-((s * w) ^ 2 * u / (2 * (1 + δ))))
          * (xiSliceReal t (s * w) * (u - Real.log 2 - 2 * E₈) ^ N / N.factorial
            * (1 / (40 * Real.pi * Real.sqrt (2 * u)))) := by rw [hQ']; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
  · -- the inner region
    intro w hw
    have hx : |s * w| < 1 / 2 := by
      rw [abs_mul, abs_of_pos hs0, ← lt_div_iff₀' hs0]
      exact abs_lt.mpr ⟨hw.1, hw.2⟩
    have hb := hinner t ht80 (s * w) hx N hN1 (by rw [← hudef]; exact hNu)
    rw [← hudef, ← hEdef, show 1 / 2 + 2 * (δ / 8) = 1 / 2 + δ / 4 by ring, ← hS₀] at hb
    rw [hFre]
    have hg1 : Real.exp (-(w ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg w])
    have hg0 := Real.exp_pos (-(w ^ 2 / 2))
    have hre1 : |(iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re| / N.factorial
        ≤ B₀ := by
      rw [hB₀]
      refine le_trans (div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) hfact0.le) ?_
      convert hb using 2
    have habs : |Real.exp (-(w ^ 2 / 2))
        * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial)| ≤ B₀ := by
      rw [abs_mul, abs_of_pos hg0, abs_div, abs_of_pos hfact0]
      calc Real.exp (-(w ^ 2 / 2)) * (|(iteratedDeriv N (xiSliceProduct t)
            ((s * w : ℝ) : ℂ)).re| / N.factorial)
          ≤ 1 * (|(iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re| / N.factorial) :=
            mul_le_mul_of_nonneg_right hg1 (by positivity)
        _ ≤ B₀ := by rw [one_mul]; exact hre1
    linarith [neg_abs_le (Real.exp (-(w ^ 2 / 2))
      * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial))]
  · -- outside the inner region
    intro w hw
    have hx : 1 / 2 ≤ |s * w| := by
      rw [abs_mul, abs_of_pos hs0, ← div_le_iff₀' hs0]
      by_contra hcon
      push Not at hcon
      exact hw (abs_lt.mp hcon)
    rw [hFre]
    have h0 := re_iteratedDeriv_xiSliceProduct_even_nonneg t m hx
    rw [← hNdef] at h0
    exact mul_nonneg (Real.exp_pos _).le (div_nonneg h0 hfact0.le)
  -- the comparison
  have hcmp := heat_window_comparison hδ hδ1 hC hE0.le hE₈0.le hu0 hu2
    (by rw [← hKdef]; exact hKu) hN1 hNu
  have hpos : 0 < ((1 + δ) / s - (1 + δ / 2) / s) * P₀ - 2 * (1 / 2 / s) * B₀ := by
    have e : ((1 + δ) / s - (1 + δ / 2) / s) * P₀ - 2 * (1 / 2 / s) * B₀
        = (δ * P₀ - 2 * B₀) / (2 * s) := by field_simp; ring
    rw [e]
    refine div_pos ?_ (by positivity)
    rw [hP₀, hB₀]
    rw [← hQ] at hcmp
    have h := mul_lt_mul_of_pos_left hcmp hS₀0
    rw [sub_pos]
    calc 2 * (C * S₀ * (Real.exp (N - δ / 8 * u) * ((u + 2 * E) / N) ^ N))
        = S₀ * (2 * (C * (Real.exp (N - δ / 8 * u) * ((u + 2 * E) / N) ^ N))) := by ring
      _ < S₀ * (δ * (Real.exp (u * (δ / 4 - δ ^ 2 / 8) - 2 * (Real.log 2 + 2 * E)) * Q)) := h
      _ = δ * (S₀ * Real.exp (u * (δ / 4 - δ ^ 2 / 8) - 2 * (Real.log 2 + 2 * E)) * Q) := by
          ring
  have hT := lt_of_lt_of_le hpos (le_of_le_of_eq hwin hre)
  rw [Complex.re_ofReal_mul] at hT
  have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hTre : 0 < (xiSliceHeatTransfer lam 0 t N).re := pos_of_mul_pos_right hT hsq.le
  exact Complex.lt_def.mpr ⟨hTre, (xiSliceHeatTransfer_im_eq_zero hlam0.le t N).symm⟩

/-- **Every even order at heat `(1+δ)/log t`.** -/
theorem exists_xiSliceHeatTransfer_pos_at_heat_one_add_over_log {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ m : ℕ,
      0 < xiSliceHeatTransfer ((1 + δ) / Real.log t) 0 t (2 * m) := by
  obtain ⟨t₁, ht₁, hlow⟩ := exists_xiSliceHeatTransfer_pos_low_order hδ hδ1
  obtain ⟨K₁, hK₁⟩ := exists_xiSliceCoeff_pos_above_quarter_log (ε := 1 / 4) (by norm_num)
  refine ⟨max t₁ (Real.exp (2 * |K₁| + 2)), le_trans ht₁ (le_max_left _ _), fun t ht m => ?_⟩
  have ht1 : t₁ ≤ t := le_trans (le_max_left _ _) ht
  have htK : Real.exp (2 * |K₁| + 2) ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : 0 < t := by linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log t := ⟨_, rfl⟩
  have hℓK : 2 * |K₁| + 2 ≤ ℓ := by
    rw [hℓ, ← Real.log_exp (2 * |K₁| + 2)]; exact Real.log_le_log (Real.exp_pos _) htK
  have hℓ0 : 0 < ℓ := by linarith [abs_nonneg K₁]
  rw [← hℓ]
  have hlam0 : 0 < (1 + δ) / ℓ := by positivity
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    rw [mul_zero]
    exact xiSliceHeatTransfer_zero_order_pos hlam0 t
  by_cases hm : (2 * m : ℝ) ≤ ℓ
  · rw [hℓ] at hm ⊢
    exact hlow t ht1 m hm0 hm
  push Not at hm
  -- high orders: every slice coefficient involved is positive
  have hcoef : ∀ k : ℕ, m ≤ k → 0 < xiSliceCoeff t (2 * k) := by
    intro k hk
    have hk' : (m : ℝ) ≤ k := by exact_mod_cast hk
    refine hK₁ t ht0.le k (max_le ?_ ?_)
    · have : (K₁ : ℝ) ≤ |K₁| := le_abs_self K₁
      linarith
    · rw [← hℓ]; linarith
  have hT := hasSum_xiSliceHeatTransfer_kernelSliceMoment hlam0.le 0 t (2 * m)
  simp only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] at hT
  have hterm : ∀ k : ℕ, 0 ≤ ((((((1 + δ) / ℓ) / 2) ^ k / k.factorial *
      ((2 * m + 2 * k).factorial / (2 * m).factorial) : ℝ) : ℂ) *
        xiSliceCoeff t (2 * m + 2 * k)) := by
    intro k
    refine mul_nonneg (Complex.zero_le_real.mpr (by positivity)) ?_
    rw [show 2 * m + 2 * k = 2 * (m + k) by ring]
    exact (hcoef (m + k) (by omega)).le
  have h0 := le_hasSum hT 0 fun j _ => hterm j
  have hfac : ((2 * m).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero, add_zero,
    div_self hfac, one_mul, Complex.ofReal_one] at h0
  exact lt_of_lt_of_le (hcoef m le_rfl) h0

/-- **Heat `(1+δ)/log |t|` makes every heated slice coefficient positive.**  For `δ ∈ (0, 1]` there is
`t₀` such that for `|t| ≥ t₀`, every heat `λ ≥ (1+δ)/log |t|` and every `m`, `T_{2m}(λ, 0, t) > 0`. -/
theorem exists_xiSliceHeatTransfer_pos_heat_one_add_over_log {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ |t| → ∀ lam : ℝ, (1 + δ) / Real.log |t| ≤ lam →
      ∀ m : ℕ, 0 < xiSliceHeatTransfer lam 0 t (2 * m) := by
  obtain ⟨t₀, ht₀, h⟩ := exists_xiSliceHeatTransfer_pos_at_heat_one_add_over_log hδ hδ1
  refine ⟨t₀, ht₀, fun t ht lam hlam m => ?_⟩
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlam
  have key : 0 < xiSliceHeatTransfer lam 0 |t| (2 * m) := by
    have hshift := hasSum_xiSliceHeatTransfer_shift hlam 0 |t| (2 * m)
    have hterm : ∀ k : ℕ, 0 ≤ ((((lam - (1 + δ) / Real.log |t|) / 2) ^ k / k.factorial *
        ((2 * m + 2 * k).factorial / (2 * m).factorial) : ℝ) : ℂ) *
          xiSliceHeatTransfer ((1 + δ) / Real.log |t|) 0 |t| (2 * m + 2 * k) := by
      intro k
      have hd : 0 ≤ (lam - (1 + δ) / Real.log |t|) / 2 := by linarith
      refine mul_nonneg (Complex.zero_le_real.mpr (by positivity)) ?_
      rw [show 2 * m + 2 * k = 2 * (m + k) by ring]
      exact (h |t| ht (m + k)).le
    have h0 := le_hasSum hshift 0 fun j _ => hterm j
    have hfac : ((2 * m).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero, add_zero,
      div_self hfac, one_mul, Complex.ofReal_one] at h0
    exact lt_of_lt_of_le (h |t| ht m) h0
  rcases le_total 0 t with htn | htn
  · rwa [abs_of_nonneg htn] at key
  · rw [abs_of_nonpos htn] at key
    rw [← neg_neg t, xiSliceHeatTransfer_neg_height hlam0]
    exact key

end

end RHTower.DeBruijn
