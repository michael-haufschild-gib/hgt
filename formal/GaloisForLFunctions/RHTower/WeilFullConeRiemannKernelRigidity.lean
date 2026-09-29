import GaloisForLFunctions.RHTower.SelbergSymbolCriticalStrip
import GaloisForLFunctions.RHTower.WeilNearRadicalDimension
import GaloisForLFunctions.RHTower.RadicalDetectionKernel
import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw
import GaloisForLFunctions.HTGeometry.SmoothTransitionDerivBound

/-!
# Riemann's kernel is a positive null vector: no Weil-positive completion majorizes `Λ`

The *full* Weil functional of `ζ`'s archimedean datum, with pole weight `1`, applied to a test `k`
and prime weights `lam`, is
`h(i/2) + h(−i/2) − Σ_{n ≥ 2} lam(n) n^{−1/2}(k(log n) + k(−log n)) + (1/2π)∫ h γ`, `h = k̂`
(`weilFullFunctional`). For `lam = Λ` it is the right side of the explicit formula, so on
autocorrelations `k = f ⋆ f̃` it equals the zero side `W(f,f)` (`zeta_W_eq_weilFullFunctional`).
Weil positivity of `lam` (`WeilPositiveFull`) asks for nonnegative real part on every
autocorrelation of a `C²` compactly supported test. No polar constraint is imposed.

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_ge`, unconditional). If `lam` is Weil-positive
and `lam(n) ≥ Λ(n)` for all `n ≥ 2`, then `lam = Λ` on `n ≥ 2`.

The test is Riemann's kernel `Φ`. Its transform is `Ξ`, which vanishes at every zero of `ζ`, so
`Φ` lies in the radical of `W`. `Φ` is positive: termwise, `Φ(u) = Σ e^{u/2}(4π²n⁴e^{4u} −
6πn²e^{2u})e^{−πn²e^{2u}} > 0` for `u ≥ 0`, and `Φ` is even. Hence every prime atom pairs with
`Φ ⋆ Φ̃` nonnegatively, and an atom where `lam` exceeds `Λ` makes the functional negative. The
truncations `Φχ_L` are genuine `C²` tests; their zero side is `O(e^{−e^{2L−2}})` by the
near-radical estimate, while the pairing with a fixed atom stays bounded below.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-! ## Positivity of Riemann's kernel -/

theorem riemannCuspPoly_eval (Y : ℝ) :
    riemannCuspPoly.eval Y = 4 * π ^ 2 * Y ^ 2 - 6 * π * Y := by
  simp only [riemannCuspPoly, cuspDeriv, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_one, Polynomial.derivative_sub, Polynomial.eval_zero,
    Polynomial.derivative_zero]
  ring

theorem cuspTerm_riemannCuspPoly_pos {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 ≤ u) :
    0 < cuspTerm riemannCuspPoly n u := by
  unfold cuspTerm
  rw [riemannCuspPoly_eval]
  have hY : 1 ≤ (n : ℝ) ^ 2 * Real.exp (2 * u) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by exact_mod_cast hn)) (Real.one_le_exp (by linarith))
  have hπ := Real.pi_gt_three
  have hpos : 0 < 4 * π ^ 2 * ((n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 -
      6 * π * ((n : ℝ) ^ 2 * Real.exp (2 * u)) := by
    set Y := (n : ℝ) ^ 2 * Real.exp (2 * u)
    have h1 : 0 < 4 * π * Y - 6 := by nlinarith
    have h2 : 0 < π * Y := by positivity
    nlinarith
  have := Real.exp_pos (u / 2)
  have := Real.exp_pos (-π * ((n : ℝ) ^ 2 * Real.exp (2 * u)))
  positivity

theorem cuspSeries_riemannCuspPoly_pos {u : ℝ} (hu : 0 ≤ u) : 0 < cuspSeries riemannCuspPoly u := by
  unfold cuspSeries
  have h0 := cuspTerm_riemannCuspPoly_pos (n := 0 + 1) le_rfl hu
  have hle := (summable_cuspTerm riemannCuspPoly u).le_tsum 0
    (fun j _ => (cuspTerm_riemannCuspPoly_pos (by omega) hu).le)
  linarith

/-- Riemann's kernel, as a real function of `|u|`. -/
def riemannKernelReal (u : ℝ) : ℝ := cuspSeries riemannCuspPoly |u|

theorem riemannKernelReal_pos (u : ℝ) : 0 < riemannKernelReal u :=
  cuspSeries_riemannCuspPoly_pos (abs_nonneg u)

theorem riemannPhiKernel_eq_ofReal (u : ℝ) : riemannPhiKernel u = (riemannKernelReal u : ℂ) := by
  unfold riemannKernelReal
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu, riemannPhiKernel_eq_cuspSeries]
  · rw [abs_of_neg hu, ← riemannPhiKernel_eq_cuspSeries, riemannPhiKernel_neg]

theorem continuous_riemannKernelReal : Continuous riemannKernelReal := by
  have h : riemannKernelReal = fun u => (riemannPhiKernel u).re := by
    funext u; rw [riemannPhiKernel_eq_ofReal, Complex.ofReal_re]
  rw [h]
  exact Complex.continuous_re.comp continuous_riemannPhiKernel

/-! ## The truncated kernel -/

/-- The truncated Riemann kernel `Φ χ_L`, a near-radical `C²` test supported in `[−L, L]`. -/
def truncatedRiemannKernel (L : ℝ) : ℝ → ℂ := nearRadicalTest L (fun _ : Fin 1 => (1 : ℂ))

/-- The real profile `Φ χ_L`. -/
def truncatedRiemannKernelReal (L u : ℝ) : ℝ := riemannKernelReal u * bulkCutoff L u

theorem truncatedRiemannKernel_eq (L u : ℝ) :
    truncatedRiemannKernel L u = (truncatedRiemannKernelReal L u : ℂ) := by
  unfold truncatedRiemannKernel nearRadicalTest kernelComb truncatedRiemannKernelReal
  rw [Fin.sum_univ_one, one_mul]
  have h0 : riemannKernelDeriv ((0 : Fin 1) : ℕ) u = riemannPhiKernel u := by
    rw [show ((0 : Fin 1) : ℕ) = 0 from rfl, riemannKernelDeriv_zero]
  rw [h0, riemannPhiKernel_eq_ofReal]
  push_cast
  ring

theorem truncatedRiemannKernelReal_nonneg (L u : ℝ) : 0 ≤ truncatedRiemannKernelReal L u :=
  mul_nonneg (riemannKernelReal_pos u).le (bulkCutoff_nonneg L u)

theorem continuous_truncatedRiemannKernelReal (L : ℝ) :
    Continuous (truncatedRiemannKernelReal L) :=
  continuous_riemannKernelReal.mul (contDiff_bulkCutoff L (n := 0)).continuous

theorem hasCompactSupport_truncatedRiemannKernel (L : ℝ) :
    HasCompactSupport (truncatedRiemannKernel L) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (tsupport_nearRadicalTest L _)

theorem hasCompactSupport_truncatedRiemannKernelReal (L : ℝ) :
    HasCompactSupport (truncatedRiemannKernelReal L) := by
  have h := hasCompactSupport_truncatedRiemannKernel L
  refine h.mono' (fun u hu => subset_tsupport _ ?_)
  rw [Function.mem_support] at hu ⊢
  rw [truncatedRiemannKernel_eq]
  exact_mod_cast hu

/-- The autocorrelation of the truncated kernel is real: `k(x) = ∫ Φχ_L(t) Φχ_L(t − x) dt`. -/
theorem weilTest_truncatedRiemannKernel_eq (L x : ℝ) :
    EF.weilTest (truncatedRiemannKernel L) (truncatedRiemannKernel L) x =
      ((∫ t, truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - x) : ℝ) : ℂ) := by
  unfold EF.weilTest convolution EF.tilde
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', truncatedRiemannKernel_eq, Complex.conj_ofReal]
  rw [show -(x - t) = t - x by ring]
  push_cast
  ring

theorem integrable_truncatedRiemannKernel_prod (L x : ℝ) :
    Integrable (fun t => truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - x)) :=
  ((continuous_truncatedRiemannKernelReal L).mul
    ((continuous_truncatedRiemannKernelReal L).comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
    ((hasCompactSupport_truncatedRiemannKernelReal L).mul_right)

theorem weilTest_truncatedRiemannKernel_re_nonneg (L x : ℝ) :
    0 ≤ (EF.weilTest (truncatedRiemannKernel L) (truncatedRiemannKernel L) x).re := by
  rw [weilTest_truncatedRiemannKernel_eq, Complex.ofReal_re]
  exact integral_nonneg fun t =>
    mul_nonneg (truncatedRiemannKernelReal_nonneg L t) (truncatedRiemannKernelReal_nonneg L _)

/-- The pairing with a fixed atom `c > 0` is bounded below uniformly in the truncation. -/
theorem exists_weilTest_truncatedRiemannKernel_ge {c : ℝ} (hc : 0 < c) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ L : ℝ, c + 1 ≤ L →
      c₀ ≤ (EF.weilTest (truncatedRiemannKernel L) (truncatedRiemannKernel L) c).re := by
  let g : ℝ → ℝ := fun t => riemannKernelReal t * riemannKernelReal (t - c)
  have hgc : Continuous g :=
    continuous_riemannKernelReal.mul (continuous_riemannKernelReal.comp (continuous_id.sub continuous_const))
  refine ⟨∫ t in (0:ℝ)..c, g t,
    intervalIntegral.intervalIntegral_pos_of_pos_on (hgc.intervalIntegrable 0 c)
      (fun t _ => mul_pos (riemannKernelReal_pos t) (riemannKernelReal_pos _)) hc, fun L hL => ?_⟩
  rw [weilTest_truncatedRiemannKernel_eq, Complex.ofReal_re]
  have hsub := setIntegral_le_integral (s := Ioc 0 c) (integrable_truncatedRiemannKernel_prod L c)
    (Filter.Eventually.of_forall fun t =>
      mul_nonneg (truncatedRiemannKernelReal_nonneg L t) (truncatedRiemannKernelReal_nonneg L _))
  refine le_trans (le_of_eq ?_) hsub
  rw [intervalIntegral.integral_of_le hc.le]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  have ht1 : |t| ≤ L - 1 := by rw [abs_of_pos ht.1]; linarith [ht.2]
  have ht2 : |t - c| ≤ L - 1 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.2])]; linarith [ht.1]
  simp only [g, truncatedRiemannKernelReal, bulkCutoff_eq_one ht1, bulkCutoff_eq_one ht2, mul_one]

/-! ## The near-radical estimate for the truncated kernel -/

theorem exists_integral_norm_sq_truncatedRiemannKernel_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ L : ℝ, ∫ u, ‖truncatedRiemannKernel L u‖ ^ 2 ≤ M := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := 1) zero_le_one
  have hint : Integrable (fun u : ℝ => C ^ 2 * Real.exp (-|u|)) := by
    simpa [neg_mul, one_mul] using integrable_exp_neg_abs.const_mul (C ^ 2)
  refine ⟨∫ u : ℝ, C ^ 2 * Real.exp (-|u|), integral_nonneg fun _ => by positivity, fun L => ?_⟩
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity) hint
    (Filter.Eventually.of_forall fun u => ?_)
  show ‖truncatedRiemannKernel L u‖ ^ 2 ≤ C ^ 2 * Real.exp (-|u|)
  have hΦ := hC u
  rw [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (riemannKernelReal_pos u)] at hΦ
  rw [truncatedRiemannKernel_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (truncatedRiemannKernelReal_nonneg L u)]
  have hb := bulkCutoff_le_one L u
  have hb0 := bulkCutoff_nonneg L u
  have hr := riemannKernelReal_pos u
  have hle : truncatedRiemannKernelReal L u ≤ C * Real.exp (-|u|) := by
    unfold truncatedRiemannKernelReal
    calc riemannKernelReal u * bulkCutoff L u ≤ riemannKernelReal u * 1 :=
          mul_le_mul_of_nonneg_left hb hr.le
      _ ≤ C * Real.exp (-|u|) := by simpa [one_mul] using hΦ
  have hsq : (C * Real.exp (-|u|)) ^ 2 ≤ C ^ 2 * Real.exp (-|u|) := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg u))
    have he0 := Real.exp_pos (-|u|)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg C)
  calc truncatedRiemannKernelReal L u ^ 2 ≤ (C * Real.exp (-|u|)) ^ 2 :=
        pow_le_pow_left₀ (truncatedRiemannKernelReal_nonneg L u) hle 2
    _ ≤ C ^ 2 * Real.exp (-|u|) := hsq

/-- The zero side of the truncated kernel tends to zero. -/
theorem exists_norm_W_truncatedRiemannKernel_le {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ‖zetaZeroConfig.W (truncatedRiemannKernel L) (truncatedRiemannKernel L)‖ ≤ ε := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨M, hM0, hM⟩ := exists_integral_norm_sq_truncatedRiemannKernel_le
  set S := zetaInvSqSum with hS
  have hS0 : 0 ≤ S := zetaInvSqSum_nonneg
  set Ystar := max (max 100 (Real.log (720 * nearRadicalConst S Λ + 1)))
    (Real.log ((M + 1) / ε)) with hYstar
  refine ⟨1 + |Real.log Ystar| / 2 + 1, fun L hL => ?_⟩
  set Y₀ := Real.exp (2 * (L - 1)) with hY₀def
  have hYstar_pos : 0 < Ystar := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hY₀ge : Ystar ≤ Y₀ := by
    have : Real.log Ystar ≤ 2 * (L - 1) := by
      have := le_abs_self (Real.log Ystar); linarith
    calc Ystar = Real.exp (Real.log Ystar) := (Real.exp_log hYstar_pos).symm
      _ ≤ Y₀ := Real.exp_le_exp.mpr this
  have hY100 : 100 ≤ Y₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY₀ge
  have hYlog : Real.log (720 * nearRadicalConst S Λ + 1) ≤ Y₀ :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY₀ge
  have hYε : Real.log ((M + 1) / ε) ≤ Y₀ := le_trans (le_max_right _ _) hY₀ge
  have hY40 : 40 ≤ Y₀ := by linarith
  have hkY : ((0 + 2 : ℕ) : ℝ) + 1 ≤ Y₀ / 10 := by push_cast; linarith
  have hW := norm_W_nearRadicalTest_le_ratio (K := 0) L (fun _ : Fin 1 => (1 : ℂ)) hΛ hY40 hkY
  rw [← hY₀def, ← hS] at hW
  have hratio := nearRadical_ratio_le (k := 0 + 2) hS0 hΛ0 hkY hY100 hYlog
  have hI : 0 ≤ ∫ u : ℝ, ‖nearRadicalTest L (fun _ : Fin 1 => (1 : ℂ)) u‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  have hIM : ∫ u : ℝ, ‖nearRadicalTest L (fun _ : Fin 1 => (1 : ℂ)) u‖ ^ 2 ≤ M := hM L
  have hexp : Real.exp (-Y₀) * (M + 1) ≤ ε := by
    have h1 : (M + 1) / ε ≤ Real.exp Y₀ := by
      calc (M + 1) / ε = Real.exp (Real.log ((M + 1) / ε)) :=
            (Real.exp_log (div_pos (by linarith) hε)).symm
        _ ≤ Real.exp Y₀ := Real.exp_le_exp.mpr hYε
    rw [div_le_iff₀ hε] at h1
    have h2 : Real.exp (-Y₀) * Real.exp Y₀ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-Y₀)).le
    nlinarith [Real.exp_pos (-Y₀)]
  calc ‖zetaZeroConfig.W (truncatedRiemannKernel L) (truncatedRiemannKernel L)‖
      ≤ Real.exp (-Y₀) * ∫ u : ℝ, ‖nearRadicalTest L (fun _ : Fin 1 => (1 : ℂ)) u‖ ^ 2 :=
        hW.trans (mul_le_mul_of_nonneg_right hratio hI)
    _ ≤ Real.exp (-Y₀) * (M + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ ≤ ε := hexp

/-! ## The full Weil functional -/

/-- The full Weil functional of `ζ`'s archimedean datum with prime weights `lam` on `n ≥ 2` and
pole weight `1`, applied to a test `k`. -/
def weilFullFunctional (lam : ℕ → ℝ) (k : ℝ → ℂ) : ℂ :=
  paperFT k (I / 2) + paperFT k (-I / 2)
  - ∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))
  + (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ)

/-- Weil positivity with the pole term: nonnegative real part on every autocorrelation of a `C²`
compactly supported test. -/
def WeilPositiveFull (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
    0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re

theorem weilFullFunctional_vonMangoldt (k : ℝ → ℂ) :
    weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) k = EF.literatureRHS k := by
  unfold weilFullFunctional EF.literatureRHS
  congr 3
  funext n
  by_cases hn : 2 ≤ n
  · rw [if_pos hn]
  · rw [if_neg hn]
    have h0 : ArithmeticFunction.vonMangoldt n = 0 := by
      interval_cases n <;> simp
    rw [h0]
    simp

/-- A compactly supported test vanishes at `±log n` for all large `n`. -/
theorem exists_forall_log_eq_zero {k : ℝ → ℂ} (hk : HasCompactSupport k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0 := by
  obtain ⟨R, hR⟩ := hk.isCompact.isBounded.subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (|R| + 1))
  refine ⟨N, fun n hn => ?_⟩
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := lt_of_lt_of_le (lt_trans (Real.exp_pos _) hN) hnR
  have hlog : |R| + 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hpos]; linarith
  have hout : ∀ x : ℝ, |R| < |x| → k x = 0 := by
    intro x hx
    by_contra hne
    have hmem := hR (subset_tsupport k hne)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
    linarith [le_abs_self R]
  have hl0 : 0 < Real.log n := by linarith [abs_nonneg R]
  exact ⟨hout _ (by rw [abs_of_pos hl0]; linarith),
    hout _ (by rw [abs_neg, abs_of_pos hl0]; linarith)⟩

theorem summable_primeAtoms (c : ℕ → ℝ) {k : ℝ → ℂ} (hk : HasCompactSupport k) :
    Summable fun n : ℕ => ((c n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
  obtain ⟨N, hN⟩ := exists_forall_log_eq_zero hk
  refine summable_of_ne_finset_zero (s := Finset.range N) (fun n hn => ?_)
  rw [Finset.mem_range, not_lt] at hn
  rw [(hN n hn).1, (hN n hn).2, add_zero, mul_zero]

/-- The full functional of `lam` is that of `Λ` minus the pairing with the weight difference. -/
theorem weilFullFunctional_eq_sub (lam : ℕ → ℝ) {k : ℝ → ℂ} (hk : HasCompactSupport k) :
    weilFullFunctional lam k = EF.literatureRHS k -
      ∑' n : ℕ, ((if 2 ≤ n then (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n else 0 : ℝ)
        : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
  rw [← weilFullFunctional_vonMangoldt]
  unfold weilFullFunctional
  have hs1 := summable_primeAtoms (fun n => if 2 ≤ n then lam n / Real.sqrt n else 0) hk
  have hs2 := summable_primeAtoms
    (fun n => if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) hk
  have hsplit : (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))) =
      (∑' n : ℕ, ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0 : ℝ)
        : ℂ) * (k (Real.log n) + k (-Real.log n))) +
      ∑' n : ℕ, ((if 2 ≤ n then (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n else 0 : ℝ)
        : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
    rw [← hs2.tsum_add (summable_primeAtoms _ hk)]
    refine tsum_congr fun n => ?_
    by_cases hn : 2 ≤ n
    · simp only [if_pos hn]; push_cast; ring
    · simp only [if_neg hn]; push_cast; ring
  rw [hsplit]
  ring

/-- **Explicit formula.** On autocorrelations, the full functional of `Λ` is the zero side. -/
theorem zeta_W_eq_weilFullFunctional {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    zetaZeroConfig.W f f =
      weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (EF.weilTest f f) := by
  rw [weilFullFunctional_vonMangoldt]
  set k := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨-, heq⟩ := WeilEF.EF_lit_zetaZeroConfig k hkd hkc
  have hfac := EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc
  have hterm : (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * paperFT k (gammaOf ρ)) =
      fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f ρ := by
    ext ρ; simp only [ZeroConfig.Wsummand, hk, hfac, mul_assoc]
  rw [ZeroConfig.W, ← hterm, heq]

/-! ## Order rigidity from above -/

/-- **No Weil-positive completion majorizes `Λ`.** If `lam` is Weil-positive with the pole term
and `lam(n) ≥ Λ(n)` for all `n ≥ 2`, then `lam(n) = Λ(n)` for all `n ≥ 2`. Unconditional. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_ge {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hge : ∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  by_contra hne
  push Not at hne
  obtain ⟨n₀, hn₀, hne₀⟩ := hne
  have hd : 0 < lam n₀ - ArithmeticFunction.vonMangoldt n₀ :=
    lt_of_le_of_ne (sub_nonneg.mpr (hge n₀ hn₀)) (sub_ne_zero.mpr hne₀).symm
  have hn₀R : (1 : ℝ) < n₀ := by exact_mod_cast (show 1 < n₀ by omega)
  set c := Real.log n₀ with hcdef
  have hc : 0 < c := Real.log_pos hn₀R
  have hsq : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by linarith)
  set δ := (lam n₀ - ArithmeticFunction.vonMangoldt n₀) / Real.sqrt n₀ with hδ
  have hδ0 : 0 < δ := div_pos hd hsq
  obtain ⟨c₀, hc₀, hc₀L⟩ := exists_weilTest_truncatedRiemannKernel_ge hc
  obtain ⟨L₀, hL₀⟩ := exists_norm_W_truncatedRiemannKernel_le (ε := δ * c₀ / 2) (by positivity)
  set L := max L₀ (c + 1) with hL
  have hLc : c + 1 ≤ L := le_max_right _ _
  have hWL := hL₀ L (le_max_left _ _)
  set f := truncatedRiemannKernel L with hf
  have hfd : ContDiff ℝ 2 f := contDiff_nearRadicalTest L _
  have hfc : HasCompactSupport f := hasCompactSupport_truncatedRiemannKernel L
  set k := EF.weilTest f f with hk
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  have hpos := hW f hfd hfc
  rw [weilFullFunctional_eq_sub lam hkc, ← weilFullFunctional_vonMangoldt,
    ← zeta_W_eq_weilFullFunctional hfd hfc] at hpos
  -- the prime pairing
  set a : ℕ → ℝ := fun n => if 2 ≤ n then (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n
    else 0 with ha
  have ha0 : ∀ n, 0 ≤ a n := by
    intro n
    simp only [ha]
    split_ifs with h2
    · exact div_nonneg (sub_nonneg.mpr (hge n h2)) (Real.sqrt_nonneg _)
    · exact le_rfl
  have hsum := summable_primeAtoms a hkc
  have hre_term : ∀ n, 0 ≤ (((a n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re := by
    intro n
    rw [Complex.re_ofReal_mul, Complex.add_re]
    exact mul_nonneg (ha0 n) (add_nonneg (weilTest_truncatedRiemannKernel_re_nonneg L _)
      (weilTest_truncatedRiemannKernel_re_nonneg L _))
  have hsumre : Summable fun n : ℕ => (((a n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re :=
    (Complex.reCLM.summable hsum)
  have hlow : δ * c₀ ≤ (∑' n : ℕ, ((a n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re := by
    rw [Complex.re_tsum hsum]
    refine le_trans ?_ (hsumre.le_tsum n₀ (fun j _ => hre_term j))
    rw [Complex.re_ofReal_mul, Complex.add_re]
    have han : a n₀ = δ := by simp only [ha, if_pos hn₀, hδ]
    rw [han]
    have hk1 : c₀ ≤ (k c).re := hc₀L L hLc
    have hk2 : 0 ≤ (k (-c)).re := weilTest_truncatedRiemannKernel_re_nonneg L _
    have := mul_le_mul_of_nonneg_left hk1 hδ0.le
    nlinarith
  have hWre := Complex.re_le_norm (zetaZeroConfig.W f f)
  rw [Complex.sub_re] at hpos
  change 0 ≤ (zetaZeroConfig.W f f).re -
    (∑' n : ℕ, ((a n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re at hpos
  have : ‖zetaZeroConfig.W f f‖ ≤ δ * c₀ / 2 := hWL
  nlinarith

end

end RHTower
