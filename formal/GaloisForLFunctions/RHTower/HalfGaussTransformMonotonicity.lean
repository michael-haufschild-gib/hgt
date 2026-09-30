import GaloisForLFunctions.RHTower.HalfGaussTransformDerivative

/-!
# A monotonicity criterion for one-sided Gaussian averages

For `Q(y) = ∫_0^∞ g_t(w − y) F(w) dw` with derivative `D(y) = ∫_0^∞ ((w − y)/(2t)) g_t(w − y) F(w) dw`:

* **Integration by parts on a window.** On `[w₁, W]`,
  `∫_{w₁}^{W} ((w − y)/(2t)) g_t(w − y) F = g_t(w₁ − y) F(w₁) − g_t(W − y) F(W) + ∫_{w₁}^{W} g_t(w − y) F'`
  (`integral_Ioc_slope_eq`), so `D − aQ` only sees `F' − aF` on the window, plus the two boundary
  values and the parts of `D − aQ` outside the window.
* **Positivity.** If `‖Q − Main‖ ≤ E₁`, `‖D − aQ‖ ≤ E₂`, `E₁ < ‖Main‖` and `E₂ < Re a (‖Main‖ − E₁)`
  then `Re(D Q̄) > 0` (`re_mul_conj_pos_of_estimates`).
* **Monotonicity.** If `Re(D Q̄) > 0` on `[−b, b]`, then `‖Q(−y)‖ < ‖Q(y)‖` for `0 < y ≤ b`
  (`norm_lt_norm_of_re_mul_conj_pos`), because `(‖Q‖²)' = 2 Re(D Q̄)`.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

theorem setIntegral_Ioi_split {f : ℝ → ℂ} {w₁ W : ℝ} (h0 : 0 ≤ w₁) (h1 : w₁ ≤ W)
    (hf : IntegrableOn f (Ioi 0)) :
    ∫ w in Ioi (0 : ℝ), f w =
      (∫ w in Ioc 0 w₁, f w) + (∫ w in Ioc w₁ W, f w) + ∫ w in Ioi W, f w := by
  have hsub1 : Ioc 0 w₁ ⊆ Ioi (0 : ℝ) := Ioc_subset_Ioi_self
  have hsub2 : Ioi w₁ ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi h0
  have hsub3 : Ioc w₁ W ⊆ Ioi w₁ := Ioc_subset_Ioi_self
  have hsub4 : Ioi W ⊆ Ioi w₁ := Ioi_subset_Ioi h1
  have hd1 : Disjoint (Ioc 0 w₁) (Ioi w₁) :=
    Set.disjoint_left.mpr fun x hx hx' => (not_lt.mpr hx.2) hx'
  have hd2 : Disjoint (Ioc w₁ W) (Ioi W) :=
    Set.disjoint_left.mpr fun x hx hx' => (not_lt.mpr hx.2) hx'
  rw [← Ioc_union_Ioi_eq_Ioi h0, setIntegral_union hd1 measurableSet_Ioi (hf.mono_set hsub1)
      (hf.mono_set hsub2), ← Ioc_union_Ioi_eq_Ioi h1, setIntegral_union hd2 measurableSet_Ioi
      ((hf.mono_set hsub2).mono_set hsub3) ((hf.mono_set hsub2).mono_set hsub4)]
  ring

theorem hasDerivAt_gaussDensity {t : ℝ} (u : ℝ) :
    HasDerivAt (gaussDensity t) (-(gaussDensity t u * (u / (2 * t)))) u := by
  have h1 : HasDerivAt (fun u : ℝ => -(u ^ 2 / (4 * t))) (-(u / (2 * t))) u := by
    have h := (((hasDerivAt_id' u).pow 2).div_const (4 * t)).neg
    refine h.congr_deriv ?_
    norm_num
    ring
  have h2 := h1.exp.const_mul ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)))
  refine h2.congr_deriv ?_
  unfold gaussDensity
  ring

/-- **Integration by parts on the window `[w₁, W]`.** -/
theorem integral_Ioc_slope_eq {t : ℝ} {F F' : ℝ → ℂ} (hFd : ∀ w, HasDerivAt F (F' w) w)
    (hF' : Continuous F') (y : ℝ) {w₁ W : ℝ} (h : w₁ ≤ W) :
    ∫ w in Ioc w₁ W, (((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * F w =
      (gaussDensity t (w₁ - y) : ℂ) * F w₁ - (gaussDensity t (W - y) : ℂ) * F W +
        ∫ w in Ioc w₁ W, (gaussDensity t (w - y) : ℂ) * F' w := by
  set v : ℝ → ℂ := fun w => (gaussDensity t (w - y) : ℂ) with hv
  set v' : ℝ → ℂ := fun w => -((((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ)) : ℂ) with hv'
  have hvd : ∀ w, HasDerivAt v (v' w) w := by
    intro w
    have := ((hasDerivAt_gaussDensity (t := t) (w - y)).comp w
      ((hasDerivAt_id' w).sub_const y)).ofReal_comp
    refine this.congr_deriv ?_
    simp only [hv']
    push_cast
    ring
  have hcont_v' : Continuous v' := by
    have := continuous_gaussDensity t
    simp only [hv']
    fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := w₁) (b := W)
    (fun w _ => hFd w) (fun w _ => hvd w) (hF'.intervalIntegrable _ _)
    (hcont_v'.intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le h, intervalIntegral.integral_of_le h] at hibp
  have e1 : ∫ w in Ioc w₁ W, (((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * F w =
      -∫ w in Ioc w₁ W, F w * v' w := by
    rw [← integral_neg]
    congr 1
    funext w
    simp only [hv']
    ring
  rw [e1, hibp]
  simp only [hv]
  have e2 : ∫ w in Ioc w₁ W, F' w * (gaussDensity t (w - y) : ℂ) =
      ∫ w in Ioc w₁ W, (gaussDensity t (w - y) : ℂ) * F' w := by
    congr 1; funext w; ring
  rw [e2]
  ring

/-- **The positivity criterion.** -/
theorem re_mul_conj_pos_of_estimates {Q D Main a : ℂ} {E₁ E₂ : ℝ} (hα : 0 ≤ a.re)
    (hQ : ‖Q - Main‖ ≤ E₁) (hD : ‖D - a * Q‖ ≤ E₂) (hm : E₁ < ‖Main‖)
    (hkey : E₂ < a.re * (‖Main‖ - E₁)) : 0 < (D * starRingEnd ℂ Q).re := by
  have hQlow : ‖Main‖ - E₁ ≤ ‖Q‖ := by
    have := norm_sub_norm_le Main Q
    rw [norm_sub_rev] at this
    linarith
  have hQpos : 0 < ‖Q‖ := by linarith
  have hsplit : D * starRingEnd ℂ Q = a * (Q * starRingEnd ℂ Q) + (D - a * Q) * starRingEnd ℂ Q := by
    ring
  have hre1 : (a * (Q * starRingEnd ℂ Q)).re = a.re * ‖Q‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.re_mul_ofReal, Complex.normSq_eq_norm_sq]
  have hre2 : -(E₂ * ‖Q‖) ≤ ((D - a * Q) * starRingEnd ℂ Q).re := by
    have h := Complex.abs_re_le_norm ((D - a * Q) * starRingEnd ℂ Q)
    rw [norm_mul, Complex.norm_conj] at h
    have : ‖D - a * Q‖ * ‖Q‖ ≤ E₂ * ‖Q‖ := by gcongr
    rw [abs_le] at h
    linarith
  rw [hsplit, Complex.add_re, hre1]
  have : a.re * (‖Main‖ - E₁) ≤ a.re * ‖Q‖ := by gcongr
  nlinarith

/-- **Monotonicity of `‖Q‖`.** -/
theorem norm_lt_norm_of_re_mul_conj_pos {Q D : ℝ → ℂ} {b : ℝ}
    (hQd : ∀ y ∈ Icc (-b) b, HasDerivAt Q (D y) y)
    (hpos : ∀ y ∈ Icc (-b) b, 0 < (D y * starRingEnd ℂ (Q y)).re) {y : ℝ} (hy : 0 < y)
    (hyb : y ≤ b) : ‖Q (-y)‖ < ‖Q y‖ := by
  have hφd : ∀ x ∈ Icc (-b) b, HasDerivAt (fun x => ‖Q x‖ ^ 2) (2 * (D x * starRingEnd ℂ (Q x)).re) x := by
    intro x hx
    have := (hQd x hx).norm_sq
    refine this.congr_deriv ?_
    rw [Complex.inner]
  have hmono : StrictMonoOn (fun x => ‖Q x‖ ^ 2) (Icc (-b) b) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun x hx => (hφd x hx).continuousAt.continuousWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hφd x (Ioo_subset_Icc_self hx)).deriv]
    have := hpos x (Ioo_subset_Icc_self hx)
    linarith
  have hlt := hmono ⟨by linarith, by linarith⟩ ⟨by linarith, hyb⟩ (by linarith : -y < y)
  simp only at hlt
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt

/-- A sum `A + conj B` vanishes only if `‖A‖ = ‖B‖`. -/
theorem add_conj_ne_zero_of_norm_ne {A B : ℂ} (h : ‖A‖ ≠ ‖B‖) : A + starRingEnd ℂ B ≠ 0 := by
  intro h0
  apply h
  rw [add_eq_zero_iff_eq_neg.mp h0, norm_neg, Complex.norm_conj]

end

end RHTower.DeBruijn
