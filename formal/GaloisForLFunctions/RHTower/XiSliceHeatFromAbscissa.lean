import GaloisForLFunctions.RHTower.XiHorizontalAbsMonoCriticalScaleDensity
import GaloisForLFunctions.RHTower.XiSliceHeatRateOnePlusDelta

/-!
# The heat threshold is at most a constant times the squared abscissa

Let `S(t, ·)` be the slice `x ↦ ξ(½+x+it) ξ(½−x+it)` and `T_n(λ, 0, t)` its heated coefficients.

**Theorem** (`xiSliceHeatTransfer_nonneg_of_absMono`).  If the slice at height `t` is absolutely
monotone from `x₀ ≥ 0` (`XiHorizontalAbsMono x₀ t`), then `T_{2m}(λ, 0, t) ≥ 0` for every `m` and every
heat `λ > 0` with `λ ≥ 100 x₀²`.

So the slice heat threshold at height `t` is at most `100 x₀(t)²`, where `x₀(t)` is the
absolute-monotonicity abscissa.  With the critical-scale abscissa on almost all heights
(`exists_volume_not_xiHorizontalAbsMono_le_criticalScale`) this gives
(`eventually_volume_xiSliceHeatTransfer_fail_le`): for every `ε > 0` there is `c` such that for all
large `U`, outside a set of measure `εU` in `[U/4 + 2, U/2 − 2]`, every even heated coefficient is
`≥ 0` at every heat `λ ≥ c/log² U`.  The heat rate at almost every height is `O(1/log² t)`; at every
height it is `(1+δ)/log t` (`exists_xiSliceHeatTransfer_pos_heat_one_add_over_log`).

Proof.  In `√(2π) T_N = ∫ e^{−w²/2} S^{(N)}(√λ w)/N! dw` put `x = √λ w`.  Absolute monotonicity at
`x₀` gives, by the Taylor shift, `S^{(N)} ≥ 0` and increasing on `[x₀, ∞)`, `S^{(N)}` even for even
`N`, and `|S^{(N)}(x)| ≤ S^{(N)}(x₀ + h)` for `|x − x₀| ≤ h`.  So the integrand is `≥ 0` on `|x| ≥ x₀`,
`≥ −S^{(N)}(3x₀)/N!` on `|x| < x₀`, and `≥ e^{−(1.3)²/2} S^{(N)}(3x₀)/N!` on `x ∈ [3x₀, 3x₀ + √λ]`.
With `x₀ ≤ √λ/10` the window `w`-length `1` beats the inner `w`-length `2x₀/√λ ≤ 1/5`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexOrder Nat

namespace RHTower.DeBruijn

noncomputable section

/-- **Taylor majorant.**  If the slice is absolutely monotone from `x₀`, then
`‖S^{(N)}(x)‖ ≤ Re S^{(N)}(x₀ + h)` for real `x` with `|x − x₀| ≤ h`. -/
theorem norm_iteratedDeriv_xiSliceProduct_le_of_absMono {t x₀ x h : ℝ}
    (habs : XiHorizontalAbsMono x₀ t) (hx : |x - x₀| ≤ h) (N : ℕ) :
    ‖iteratedDeriv N (xiSliceProduct t) (x : ℂ)‖
      ≤ (iteratedDeriv N (xiSliceProduct t) ((x₀ + h : ℝ) : ℂ)).re := by
  have hh : 0 ≤ h := le_trans (abs_nonneg _) hx
  have hS := hasSum_iteratedDeriv_xiSliceProduct_shift t N (x₀ : ℂ) (x : ℂ)
  have hT := hasSum_iteratedDeriv_xiSliceProduct_shift t N (x₀ : ℂ) ((x₀ + h : ℝ) : ℂ)
  have hTre := (Complex.hasSum_re hT)
  have hreal : ∀ k, (iteratedDeriv (N + k) (xiSliceProduct t) (x₀ : ℂ))
      = (((iteratedDeriv (N + k) (xiSliceProduct t) (x₀ : ℂ)).re : ℝ) : ℂ) := fun k =>
    (Complex.ext rfl (by simp [(Complex.nonneg_iff.mp (habs (N + k))).2.symm]))
  refine hS.norm_le_of_bounded hTre fun k => ?_
  have hD0 : 0 ≤ (iteratedDeriv (N + k) (xiSliceProduct t) (x₀ : ℂ)).re :=
    (Complex.nonneg_iff.mp (habs (N + k))).1
  rw [hreal k]
  have e1 : ((x₀ + h : ℝ) : ℂ) - (x₀ : ℂ) = ((h : ℝ) : ℂ) := by push_cast; ring
  rw [e1]
  rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hD0, Complex.norm_natCast]
  have e2 : ((k ! : ℂ))⁻¹ * ((h : ℂ) ^ k * (((iteratedDeriv (N + k) (xiSliceProduct t)
      (x₀ : ℂ)).re : ℝ) : ℂ)) = ((((k ! : ℝ))⁻¹ * (h ^ k *
        (iteratedDeriv (N + k) (xiSliceProduct t) (x₀ : ℂ)).re) : ℝ) : ℂ) := by push_cast; ring
  rw [e2, Complex.ofReal_re]
  have hxk : ‖(x : ℂ) - (x₀ : ℂ)‖ ^ k ≤ h ^ k := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hx k
  have hk : (0 : ℝ) ≤ ((k ! : ℝ))⁻¹ := by positivity
  calc ((k ! : ℝ))⁻¹ * (‖(x : ℂ) - (x₀ : ℂ)‖ ^ k
        * (iteratedDeriv (N + k) (xiSliceProduct t) (x₀ : ℂ)).re)
      ≤ ((k ! : ℝ))⁻¹ * (h ^ k * (iteratedDeriv (N + k) (xiSliceProduct t) (x₀ : ℂ)).re) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxk hD0) hk
    _ = _ := rfl

/-- **Monotonicity beyond the abscissa.**  If the slice is absolutely monotone from `x₀`, then
`x ↦ Re S^{(N)}(x)` is nondecreasing on `[x₀, ∞)`. -/
theorem re_iteratedDeriv_xiSliceProduct_mono_of_absMono {t x₀ x y : ℝ}
    (habs : XiHorizontalAbsMono x₀ t) (hx : x₀ ≤ x) (hxy : x ≤ y) (N : ℕ) :
    (iteratedDeriv N (xiSliceProduct t) (x : ℂ)).re
      ≤ (iteratedDeriv N (xiSliceProduct t) (y : ℂ)).re := by
  have hS := Complex.hasSum_re (hasSum_iteratedDeriv_xiSliceProduct_shift t N (x : ℂ) (y : ℂ))
  have hterm : ∀ k, 0 ≤ (((k ! : ℂ))⁻¹ * (((y : ℂ) - (x : ℂ)) ^ k
      * iteratedDeriv (N + k) (xiSliceProduct t) (x : ℂ))).re := by
    intro k
    have hD := iteratedDeriv_xiSliceProduct_nonneg_of_le habs hx (N + k)
    have h1 : (0 : ℂ) ≤ ((k ! : ℂ))⁻¹ := by
      rw [show ((k ! : ℂ))⁻¹ = ((((k ! : ℝ))⁻¹ : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.zero_le_real.mpr (by positivity)
    have h2 : (0 : ℂ) ≤ ((y : ℂ) - (x : ℂ)) ^ k := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_pow]
      exact Complex.zero_le_real.mpr (pow_nonneg (by linarith) k)
    exact (Complex.nonneg_iff.mp (mul_nonneg h1 (mul_nonneg h2 hD))).1
  have h0 := le_hasSum hS 0 fun j _ => hterm j
  simpa using h0

/-- **Heat from the abscissa.**  If the slice at height `t` is absolutely monotone from `x₀ ≥ 0`, then
`T_{2m}(λ, 0, t) ≥ 0` for every `m` and every heat `λ > 0` with `λ ≥ 100 x₀²`. -/
theorem xiSliceHeatTransfer_nonneg_of_absMono {t x₀ lam : ℝ} (habs : XiHorizontalAbsMono x₀ t)
    (hx₀ : 0 ≤ x₀) (hlam : 0 < lam) (h100 : 100 * x₀ ^ 2 ≤ lam) (m : ℕ) :
    0 ≤ xiSliceHeatTransfer lam 0 t (2 * m) := by
  obtain ⟨N, hNdef⟩ : ∃ N, N = 2 * m := ⟨_, rfl⟩
  rw [← hNdef]
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt lam := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hlam
  have hx₀s : 10 * x₀ ≤ s := by
    have h := Real.sqrt_le_sqrt h100
    rw [show 100 * x₀ ^ 2 = (10 * x₀) ^ 2 by ring, Real.sqrt_sq (by linarith), ← hsdef] at h
    exact h
  have hc1 : x₀ / s ≤ 1 / 10 := by rw [div_le_iff₀ hs0]; linarith
  have hc0 : 0 ≤ x₀ / s := div_nonneg hx₀ hs0.le
  have hfact0 : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  -- the representation and its real part
  have hrep := xiSliceHeatTransfer_eq_integral_iteratedDeriv hlam.le t N
  have hint := integrable_gauss_mul_iteratedDeriv_xiSliceProduct hlam.le t N
  rw [← hsdef] at hrep hint
  set F : ℝ → ℂ := fun w => ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
    * (iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ) / N.factorial) with hF
  have hre : ∫ w, (F w).re = (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
      * xiSliceHeatTransfer lam 0 t N).re := by
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [hrep]; exact this
  have hFre : ∀ w, (F w).re = Real.exp (-(w ^ 2 / 2))
      * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial) := by
    intro w
    simp only [hF]
    rw [Complex.re_ofReal_mul, Complex.div_natCast_re]
  -- the comparison value `S^{(N)}(3x₀)`
  set D₃ := (iteratedDeriv N (xiSliceProduct t) ((3 * x₀ : ℝ) : ℂ)).re with hD₃
  have hD₃0 : 0 ≤ D₃ :=
    (Complex.nonneg_iff.mp (iteratedDeriv_xiSliceProduct_nonneg_of_le habs (by linarith) N)).1
  have hexp : (1 : ℝ) / 5 ≤ Real.exp (-(169 / 200)) := by
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    have h1 : Real.exp (169 / 200) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
    have h2 := Real.exp_one_lt_d9
    norm_num at h2 ⊢
    linarith
  have hwin := integral_ge_of_window (h := fun w => (F w).re) hint.re
    (a := 3 * x₀ / s) (b := 3 * x₀ / s + 1) (c := x₀ / s)
    (P := Real.exp (-(169 / 200)) * (D₃ / N.factorial)) (B := D₃ / N.factorial)
    (by linarith) hc0 (div_le_div_of_nonneg_right (by linarith) hs0.le) ?_ ?_ ?_
  rotate_left
  · -- the window
    intro w hw
    have hw0 : 0 ≤ w := le_trans (div_nonneg (by linarith) hs0.le) hw.1
    have hsw : 3 * x₀ ≤ s * w := by
      have := hw.1; rw [div_le_iff₀ hs0] at this; linarith
    have hw13 : w ≤ 13 / 10 := by
      have h3 : 3 * x₀ / s ≤ 3 / 10 := by rw [div_le_iff₀ hs0]; linarith
      linarith [hw.2]
    have hg : Real.exp (-(169 / 200)) ≤ Real.exp (-(w ^ 2 / 2)) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hmono := re_iteratedDeriv_xiSliceProduct_mono_of_absMono habs (by linarith) hsw N
    rw [← hD₃] at hmono
    show Real.exp (-(169 / 200)) * (D₃ / N.factorial) ≤ (F w).re
    rw [hFre]
    exact mul_le_mul hg (div_le_div_of_nonneg_right hmono hfact0.le)
      (div_nonneg hD₃0 hfact0.le) (Real.exp_pos _).le
  · -- the inner region
    intro w hw
    have hx : |s * w - x₀| ≤ 2 * x₀ := by
      have h1 : |s * w| < x₀ := by
        rw [abs_mul, abs_of_pos hs0, ← lt_div_iff₀' hs0]
        exact abs_lt.mpr ⟨hw.1, hw.2⟩
      rw [abs_le]; rw [abs_lt] at h1; constructor <;> linarith
    have hmaj := norm_iteratedDeriv_xiSliceProduct_le_of_absMono habs hx N
    rw [show x₀ + 2 * x₀ = 3 * x₀ by ring, ← hD₃] at hmaj
    show -(D₃ / N.factorial) ≤ (F w).re
    rw [hFre]
    have hg1 : Real.exp (-(w ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg w])
    have hg0 := Real.exp_pos (-(w ^ 2 / 2))
    have hre1 : |(iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re| / N.factorial
        ≤ D₃ / N.factorial :=
      div_le_div_of_nonneg_right ((Complex.abs_re_le_norm _).trans hmaj) hfact0.le
    have habs' : |Real.exp (-(w ^ 2 / 2))
        * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial)|
        ≤ D₃ / N.factorial := by
      rw [abs_mul, abs_of_pos hg0, abs_div, abs_of_pos hfact0]
      calc Real.exp (-(w ^ 2 / 2)) * (|(iteratedDeriv N (xiSliceProduct t)
            ((s * w : ℝ) : ℂ)).re| / N.factorial)
          ≤ 1 * (|(iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re| / N.factorial) :=
            mul_le_mul_of_nonneg_right hg1 (by positivity)
        _ ≤ D₃ / N.factorial := by rw [one_mul]; exact hre1
    linarith [neg_abs_le (Real.exp (-(w ^ 2 / 2))
      * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial))]
  · -- outside the inner region
    intro w hw
    have hx : x₀ ≤ |s * w| := by
      rw [abs_mul, abs_of_pos hs0, ← div_le_iff₀' hs0]
      by_contra hcon
      push Not at hcon
      exact hw (abs_lt.mp hcon)
    show 0 ≤ (F w).re
    rw [hFre]
    refine mul_nonneg (Real.exp_pos _).le (div_nonneg ?_ hfact0.le)
    rcases le_total 0 (s * w) with hpos | hneg
    · rw [abs_of_nonneg hpos] at hx
      exact (Complex.nonneg_iff.mp (iteratedDeriv_xiSliceProduct_nonneg_of_le habs hx N)).1
    · rw [abs_of_nonpos hneg] at hx
      rw [hNdef, ← iteratedDeriv_xiSliceProduct_neg_even, ← Complex.ofReal_neg]
      exact (Complex.nonneg_iff.mp
        (iteratedDeriv_xiSliceProduct_nonneg_of_le habs hx (2 * m))).1
  -- the comparison
  have hlow : 0 ≤ (3 * x₀ / s + 1 - 3 * x₀ / s) * (Real.exp (-(169 / 200)) * (D₃ / N.factorial))
      - 2 * (x₀ / s) * (D₃ / N.factorial) := by
    have hq : 0 ≤ D₃ / N.factorial := div_nonneg hD₃0 hfact0.le
    have h1 : 2 * (x₀ / s) * (D₃ / N.factorial) ≤ 1 / 5 * (D₃ / N.factorial) :=
      mul_le_mul_of_nonneg_right (by linarith) hq
    have h2 : 1 / 5 * (D₃ / N.factorial) ≤ Real.exp (-(169 / 200)) * (D₃ / N.factorial) :=
      mul_le_mul_of_nonneg_right hexp hq
    have e : 3 * x₀ / s + 1 - 3 * x₀ / s = 1 := by ring
    rw [e, one_mul]
    linarith
  have hT := le_trans hlow (le_of_le_of_eq hwin hre)
  rw [Complex.re_ofReal_mul] at hT
  have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hTre : 0 ≤ (xiSliceHeatTransfer lam 0 t N).re := nonneg_of_mul_nonneg_right
    (by linarith [mul_comm (Real.sqrt (2 * Real.pi)) (xiSliceHeatTransfer lam 0 t N).re]) hsq
  exact Complex.nonneg_iff.mpr ⟨hTre, (xiSliceHeatTransfer_im_eq_zero hlam.le t N).symm⟩

/-- **Heat rate `O(1/log² t)` on almost all heights.**  For every `ε > 0` there is `c ≥ 2` such that
for all large `U`, outside a set of measure at most `εU` in `[U/4 + 2, U/2 − 2]`, every even heated
slice coefficient is `≥ 0` at every heat `λ ≥ 100 c²/log² U`. -/
theorem eventually_volume_xiSliceHeatTransfer_fail_le {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 2 ≤ c ∧ ∀ᶠ U in atTop,
      volume {t ∈ Icc (U / 4 + 2) (U / 2 - 2) | ∃ lam : ℝ, 0 < lam ∧
          100 * (c / Real.log U) ^ 2 ≤ lam ∧ ∃ m : ℕ, ¬ 0 ≤ xiSliceHeatTransfer lam 0 t (2 * m)}
        ≤ ENNReal.ofReal (ε * U) := by
  obtain ⟨c, hc, hmain⟩ := eventually_volume_not_xiHorizontalAbsMono_le hε
  refine ⟨c, hc, ?_⟩
  filter_upwards [hmain, eventually_ge_atTop (1 : ℝ)] with U hU hU1
  refine le_trans (measure_mono ?_) hU
  rintro t ⟨ht, lam, hlam, h100, m, hm⟩
  refine ⟨ht, fun habs => hm ?_⟩
  exact xiSliceHeatTransfer_nonneg_of_absMono habs
    (div_nonneg (by linarith) (Real.log_nonneg hU1)) hlam h100 m

end

end RHTower.DeBruijn
