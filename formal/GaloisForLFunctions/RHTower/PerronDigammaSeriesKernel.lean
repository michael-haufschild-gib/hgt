import GaloisForLFunctions.RHTower.PerronLaplacePoleKernel
import GaloisForLFunctions.HTGeometry.DigammaGaussSeries

/-!
# The weighted Perron integral of the Gauss series of digamma

For `Re z > 0`, `c > 0`, `L ≥ 0` and `s = c + 2πiw`,

`∫ Σ_n g_n((z + s)/2) e^{sL}/s² dw = Σ_n (L/(n + 1) − 2 Q(−z − 2n))`,

where `g_n(v) = 1/(n + 1) − 1/(v + n)` is the Gauss summand (`ψ(v) = −γ + Σ_n g_n(v)`) and
`Q(b) = (e^{bL} − 1 − bL)/b²` (`integral_tsum_gaussDigammaSeriesTerm_mul_perron`).  The poles
`s = −z − 2n` of `ψ((z + s)/2)` are the trivial points of the archimedean factor; each contributes
`−2Q(−z − 2n)`.

**Proof.**  Termwise, `g_n((z + s)/2) = 1/(n + 1) − 2/(s − b_n)` with `b_n = −z − 2n`, and the
pole integral of `PerronLaplacePoleKernel` applies.  The interchange of sum and integral needs
`Σ_n ∫ |g_n| |e^{sL}/s²| dw < ∞`.  Interpolating `|g_n(v)| ≤ |v − 1|/(α(n + 1)²)` and
`|g_n(v)| ≤ 2/(α(n + 1))` (`α ≤ Re v`) gives `|g_n| ≪ (1 + |w|)^{3/4} (n + 1)^{−7/4}`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace RHTower

namespace PerronPole

/-- Interpolation of two bounds: `x ≤ A/N²` and `x ≤ B/N` give `x ≤ A^{3/4} B^{1/4}/N^{7/4}`. -/
theorem le_div_rpow_of_le_of_le {x A B N : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hN : 0 < N) (h1 : x ≤ A / N ^ 2) (h2 : x ≤ B / N) :
    x ≤ A ^ (3 / 4 : ℝ) * B ^ (1 / 4 : ℝ) / N ^ (7 / 4 : ℝ) := by
  have h4 : x ^ 4 ≤ A ^ 3 * B / N ^ 7 := by
    calc x ^ 4 = x ^ 3 * x := by ring
      _ ≤ (A / N ^ 2) ^ 3 * (B / N) :=
          mul_le_mul (pow_le_pow_left₀ hx h1 3) h2 hx (by positivity)
      _ = A ^ 3 * B / N ^ 7 := by field_simp
  have hx4 : x = (x ^ 4) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  rw [hx4]
  calc (x ^ 4) ^ (1 / 4 : ℝ) ≤ (A ^ 3 * B / N ^ 7) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) h4 (by norm_num)
    _ = A ^ (3 / 4 : ℝ) * B ^ (1 / 4 : ℝ) / N ^ (7 / 4 : ℝ) := by
      rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hB,
        ← Real.rpow_natCast A 3, ← Real.rpow_mul hA, ← Real.rpow_natCast N 7,
        ← Real.rpow_mul hN.le]
      norm_num

/-- **Gauss summand bound.**  For `0 < α ≤ 1` and `α ≤ Re v`,
`|g_n(v)| ≤ (|v − 1|/α)^{3/4} (2/α)^{1/4} / (n + 1)^{7/4}`. -/
theorem norm_gaussDigammaSeriesTerm_le {v : ℂ} {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hv : α ≤ v.re) (n : ℕ) :
    ‖gaussDigammaSeriesTerm v n‖ ≤
      (‖v - 1‖ / α) ^ (3 / 4 : ℝ) * (2 / α) ^ (1 / 4 : ℝ) / ((n : ℝ) + 1) ^ (7 / 4 : ℝ) := by
  have hv0 : 0 < v.re := hα.trans_le hv
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hvn : α * ((n : ℝ) + 1) ≤ ‖v + n‖ := by
    have h := Complex.re_le_norm (v + n)
    have hre : (v + n).re = v.re + n := by simp
    rw [hre] at h
    nlinarith
  have hvn0 : 0 < ‖v + n‖ := lt_of_lt_of_le (by positivity) hvn
  have hn1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hN]
  apply le_div_rpow_of_le_of_le (norm_nonneg _) (by positivity) (by positivity) hN
  · rw [gaussDigammaSeriesTerm_eq hv0, norm_div, norm_mul, hn1]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : ‖v - 1‖ / α * (((n : ℝ) + 1) * (α * ((n : ℝ) + 1))) =
        ‖v - 1‖ * ((n : ℝ) + 1) ^ 2 := by field_simp
    have h1 : ‖v - 1‖ / α * (((n : ℝ) + 1) * (α * ((n : ℝ) + 1))) ≤
        ‖v - 1‖ / α * (((n : ℝ) + 1) * ‖v + n‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvn hN.le) (by positivity)
    linarith
  · unfold gaussDigammaSeriesTerm
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_one, hn1, norm_div, norm_one]
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / (α * ((n : ℝ) + 1)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h2 : 1 / ‖v + n‖ ≤ 1 / (α * ((n : ℝ) + 1)) :=
      one_div_le_one_div_of_le (by positivity) hvn
    have e : 2 / α / ((n : ℝ) + 1) = 1 / (α * ((n : ℝ) + 1)) + 1 / (α * ((n : ℝ) + 1)) := by
      field_simp; ring
    linarith

/-- **The weighted Perron integral of the Gauss series.**  For `Re z > 0`, `c > 0`, `L ≥ 0`:
`∫ Σ_n g_n((z + s)/2) e^{sL}/s² dw = Σ_n (L/(n + 1) − 2 Q(b_n))`, `b_n = −z − 2n`,
`Q(b) = (e^{bL} − 1 − bL)/b²`. -/
theorem integral_tsum_gaussDigammaSeriesTerm_mul_perron {z : ℂ} (hz : 0 < z.re) {c : ℝ}
    (hc : 0 < c) {L : ℝ} (hL : 0 ≤ L) :
    ∫ w : ℝ, (∑' n : ℕ, gaussDigammaSeriesTerm ((z + contour c w) / 2) n) *
        (cexp (contour c w * L) / contour c w ^ 2) =
      ∑' n : ℕ, ((L : ℂ) / ((n : ℂ) + 1) -
        2 * ((cexp ((-z - 2 * n) * L) - 1 - (-z - 2 * n) * L) / (-z - 2 * n) ^ 2)) := by
  set P : ℝ → ℂ := fun w => cexp (contour c w * L) / contour c w ^ 2 with hP
  set b : ℕ → ℂ := fun n => -z - 2 * n with hb
  have hbre : ∀ n, (b n).re < c := fun n => by
    simp only [hb, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im]
    norm_num
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hb0 : ∀ n, b n ≠ 0 := fun n h0 => by
    have := congrArg Complex.re h0
    simp only [hb, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, Complex.zero_re] at this
    norm_num at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  set F : ℕ → ℝ → ℂ := fun n w => gaussDigammaSeriesTerm ((z + contour c w) / 2) n * P w with hF
  have hFe : ∀ n w, F n w = 1 / ((n : ℂ) + 1) * P w - 2 * (1 / (contour c w - b n) * P w) := by
    intro n w
    have hne : contour c w - b n ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0
      rw [Complex.sub_re, contour_re, Complex.zero_re] at this
      linarith [hbre n]
    have e : (z + contour c w) / 2 + n = (contour c w - b n) / 2 := by simp only [hb]; ring
    simp only [hF, gaussDigammaSeriesTerm]
    rw [e]
    field_simp
  have hint : ∀ n, Integrable (F n) := fun n => by
    have h1 : Integrable fun w => 1 / ((n : ℂ) + 1) * P w :=
      (integrable_perron_integrand hc L).const_mul _
    have h2 : Integrable fun w => 2 * (1 / (contour c w - b n) * P w) :=
      (integrable_inv_sub_mul_perron hc L (hbre n)).const_mul _
    exact (h1.sub h2).congr (Eventually.of_forall fun w => (hFe n w).symm)
  have hPint : ∫ w, P w = (L : ℂ) := by
    have hK := perron_weighted_kernel hc L
    rw [show (L : ℂ) = ((max L 0 : ℝ) : ℂ) by rw [max_eq_left hL]]
    exact hK
  have hval : ∀ n, ∫ w, F n w = (L : ℂ) / ((n : ℂ) + 1) -
      2 * ((cexp ((-z - 2 * n) * L) - 1 - (-z - 2 * n) * L) / (-z - 2 * n) ^ 2) := by
    intro n
    have h1 : Integrable fun w => 1 / ((n : ℂ) + 1) * P w :=
      (integrable_perron_integrand hc L).const_mul _
    have h2 : Integrable fun w => 2 * (1 / (contour c w - b n) * P w) :=
      (integrable_inv_sub_mul_perron hc L (hbre n)).const_mul _
    have h3 : ∫ w, 1 / (contour c w - b n) * P w =
        (cexp (b n * L) - 1 - b n * L) / b n ^ 2 :=
      integral_inv_sub_mul_perron_eq hc hL (hbre n) (hb0 n)
    rw [integral_congr_ae (Eventually.of_forall (hFe n)), integral_sub h1 h2, integral_const_mul,
      integral_const_mul, h3, hPint]
    simp only [hb]
    ring
  -- summability of the norms
  set α : ℝ := min ((z.re + c) / 2) 1 with hα
  have hα0 : 0 < α := lt_min (by linarith) one_pos
  have hα1 : α ≤ 1 := min_le_right _ _
  set K₂ : ℝ := ‖z‖ / 2 + c / 2 + π + 1 with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  set m : ℝ := min (c ^ 2) 1 with hm
  set I₀ : ℝ := ∫ w : ℝ, (1 + ‖w‖) ^ (-(5 / 4 : ℝ)) with hI₀
  have hmaj : Integrable (fun w : ℝ => (1 + ‖w‖) ^ (-(5 / 4 : ℝ))) :=
    integrable_one_add_norm (E := ℝ) (μ := volume) (r := 5 / 4) (by norm_num)
  set K₃ : ℝ := (K₂ / α) ^ (3 / 4 : ℝ) * (2 / α) ^ (1 / 4 : ℝ) with hK₃
  have hK₃0 : 0 ≤ K₃ := by positivity
  have hterm : ∀ n w, ‖gaussDigammaSeriesTerm ((z + contour c w) / 2) n‖ ≤
      K₃ / ((n : ℝ) + 1) ^ (7 / 4 : ℝ) * (1 + |w|) ^ (3 / 4 : ℝ) := by
    intro n w
    set v : ℂ := (z + contour c w) / 2 with hv
    have hvre : α ≤ v.re := by
      have : v.re = (z.re + c) / 2 := by simp [hv, contour_re]
      rw [this]; exact min_le_left _ _
    refine (norm_gaussDigammaSeriesTerm_le hα0 hα1 hvre n).trans ?_
    have hv1 : ‖v - 1‖ ≤ K₂ * (1 + |w|) := by
      have e : v - 1 = z / 2 + (c / 2 : ℝ) + ((π * w : ℝ) : ℂ) * I - 1 := by
        simp only [hv, contour]; push_cast; ring
      rw [e]
      have h1 := norm_sub_le (z / 2 + (c / 2 : ℝ) + ((π * w : ℝ) : ℂ) * I) 1
      have h2 := norm_add_le (z / 2 + (c / 2 : ℝ)) (((π * w : ℝ) : ℂ) * I)
      have h3 := norm_add_le (z / 2) ((c / 2 : ℝ) : ℂ)
      have e1 : ‖z / 2‖ = ‖z‖ / 2 := by rw [norm_div, Complex.norm_two]
      have e2 : ‖((c / 2 : ℝ) : ℂ)‖ = c / 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have e3 : ‖((π * w : ℝ) : ℂ) * I‖ = π * |w| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
          abs_of_pos Real.pi_pos]
      rw [norm_one] at h1
      have hw := abs_nonneg w
      have : K₂ * (1 + |w|) = K₂ + (‖z‖ / 2 + c / 2 + π + 1) * |w| := by rw [hK₂]; ring
      have : π * |w| ≤ (‖z‖ / 2 + c / 2 + π + 1) * |w| :=
        mul_le_mul_of_nonneg_right (by have := norm_nonneg z; linarith) hw
      have := Real.pi_pos
      linarith
    have hA : (‖v - 1‖ / α) ^ (3 / 4 : ℝ) ≤ (K₂ / α) ^ (3 / 4 : ℝ) * (1 + |w|) ^ (3 / 4 : ℝ) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hv1 hα0.le
    have hN : 0 < ((n : ℝ) + 1) ^ (7 / 4 : ℝ) := by positivity
    rw [hK₃, div_le_iff₀ hN]
    have e : (K₂ / α) ^ (3 / 4 : ℝ) * (2 / α) ^ (1 / 4 : ℝ) / ((n : ℝ) + 1) ^ (7 / 4 : ℝ) *
        (1 + |w|) ^ (3 / 4 : ℝ) * ((n : ℝ) + 1) ^ (7 / 4 : ℝ) =
        (K₂ / α) ^ (3 / 4 : ℝ) * (1 + |w|) ^ (3 / 4 : ℝ) * (2 / α) ^ (1 / 4 : ℝ) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hA (by positivity)
  have hnormint : ∀ n, ∫ w, ‖F n w‖ ≤ K₃ / ((n : ℝ) + 1) ^ (7 / 4 : ℝ) *
      Real.exp (c * L) * (2 / m) * I₀ := by
    intro n
    have hC : 0 ≤ K₃ / ((n : ℝ) + 1) ^ (7 / 4 : ℝ) := by positivity
    have hpt : ∀ w, ‖F n w‖ ≤ K₃ / ((n : ℝ) + 1) ^ (7 / 4 : ℝ) * Real.exp (c * L) * (2 / m) *
        (1 + ‖w‖) ^ (-(5 / 4 : ℝ)) := by
      intro w
      have hPn : ‖P w‖ = Real.exp (c * L) / (c ^ 2 + (2 * π * w) ^ 2) :=
        norm_perron_integrand (a := c) L w
      simp only [hF]
      rw [norm_mul, hPn, mul_comm]
      exact (mul_le_mul_of_nonneg_left (hterm n w) (by positivity)).trans
        (perron_bound_mul_rpow_le hc hC)
    calc ∫ w, ‖F n w‖ ≤ ∫ w, K₃ / ((n : ℝ) + 1) ^ (7 / 4 : ℝ) * Real.exp (c * L) * (2 / m) *
          (1 + ‖w‖) ^ (-(5 / 4 : ℝ)) := integral_mono (hint n).norm (hmaj.const_mul _) hpt
      _ = _ := by rw [integral_const_mul]
  have hsum : Summable fun n => ∫ w, ‖F n w‖ := by
    have hs := (Real.summable_one_div_nat_add_rpow 1 (7 / 4)).mpr (by norm_num)
    have hs' : Summable fun n : ℕ => K₃ / ((n : ℝ) + 1) ^ (7 / 4 : ℝ) * Real.exp (c * L) *
        (2 / m) * I₀ := by
      have := ((hs.mul_left K₃).mul_right (Real.exp (c * L))).mul_right (2 / m)
      refine (this.mul_right I₀).congr fun n => ?_
      rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      ring
    exact hs'.of_nonneg_of_le (fun n => integral_nonneg fun w => norm_nonneg _) hnormint
  calc ∫ w : ℝ, (∑' n : ℕ, gaussDigammaSeriesTerm ((z + contour c w) / 2) n) * P w
      = ∫ w, ∑' n, F n w := integral_congr_ae (Eventually.of_forall fun w => by
          simp only [hF]; rw [tsum_mul_right])
    _ = ∑' n, ∫ w, F n w := (integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = _ := tsum_congr hval

end PerronPole

end RHTower

end
