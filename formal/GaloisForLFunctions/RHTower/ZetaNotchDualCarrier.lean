import GaloisForLFunctions.RHTower.ProductAFEExact
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDerivative
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualExpansion
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiPowerBound
import GaloisForLFunctions.RHTower.ChiIncrementDifferenceJets

/-!
# The dual carrier of `|ζ(½+it)|²` on the critical line

For the critical pair `s₁ = ½+it`, `s₂ = ½−it` the exact product approximate functional
equation has the dual weight

`W_t(Y) = (1/2π) ∫ G_t(−(1+iv)) e^{(1+iv)²} Y^{−(1+iv)}/(1+iv) dv`,

with the two-ratio carrier `G_t(w) = [χ(s₁+w)/χ(s₁)]·[χ(s₂+w)/χ(s₂)]`.

This file records the three properties of `G_t` used later.

* **Height derivative.** `∂_t G_t(w) = G_t(w)·D_t(w)`, where `D_t(w)` is a difference of two
  increments of `χ'/χ` across the shift `w` (`hasDerivAt_critCarrier`).
* **Increment bound.** `‖D_t(w)‖ ≤ 20‖w‖/t` for `t ≥ 4`, `2|Im w| ≤ t`, `|Re w| ≤ 1`
  (`norm_critIncrement_le`). This is the segment inequality for `χ'/χ`, whose derivative is
  `O(1/|Im z|)` off the real axis.
* **Size.**
  - On the dual contour `w = −(1+iv)`: `‖G_t‖ ≤ (1+|t|)²(1+|v|)²`.
  - On a right contour `w = δ − iv`, `0 < δ < ½`: `‖G_t‖ ≤ K²·max(1,|t−v|)^{−δ}·max(1,|t+v|)^{−δ}`.
    Here `|χ(½+it)| = 1` and `χ` decays like `|t|^{−δ}` on `Re s = ½+δ`.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex RHTower RHTower.Sieve

/-- The two-ratio carrier of the product approximate functional equation at the critical pair
`(½+it, ½−it)` and shift `w`. -/
def critCarrier (t : ℝ) (w : ℂ) : ℂ :=
  smoothAFEZetaChiShiftRatio (linePt t) w * smoothAFEZetaChiShiftRatio (linePt (-t)) w

/-- The logarithmic height derivative of the carrier: a difference of two `χ'/χ` increments. -/
def critIncrement (t : ℝ) (w : ℂ) : ℂ :=
  I * (logDeriv zetaChi (linePt t + w) - logDeriv zetaChi (linePt t)) -
    I * (logDeriv zetaChi (linePt (-t) + w) - logDeriv zetaChi (linePt (-t)))

/-- The dual weight of the product approximate functional equation at the critical pair. -/
def critDualWeight (t Y : ℝ) : ℂ :=
  productAFEDualWeight (linePt t) (linePt (-t)) Y

theorem critDualWeight_eq (t Y : ℝ) :
    critDualWeight t Y = (1 / (2 * Real.pi)) • ∫ v : ℝ,
      critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I) := rfl

/-! ## The height derivative -/

theorem hasDerivAt_critCarrier {t : ℝ} {w : ℂ}
    (h₁ : Gammaℝ (1 - (linePt t + w)) ≠ 0) (h₁' : zetaChi (linePt t + w) ≠ 0)
    (h₂ : Gammaℝ (1 - (linePt (-t) + w)) ≠ 0) (h₂' : zetaChi (linePt (-t) + w) ≠ 0) :
    HasDerivAt (fun s : ℝ => critCarrier s w) (critCarrier t w * critIncrement t w) t := by
  have hA := hasDerivAt_smoothAFEZetaChiShiftRatio_line_logDeriv h₁ h₁'
  have hB := (hasDerivAt_smoothAFEZetaChiShiftRatio_line_logDeriv h₂ h₂').scomp t
    (hasDerivAt_neg t)
  have h := hA.mul hB
  refine h.congr_deriv ?_
  unfold critCarrier critIncrement
  simp only [Function.comp_apply, neg_smul, one_smul]
  ring

/-! ## The increment bound -/

/-- One increment of `χ'/χ` across a short shift, at height `τ` with `|τ| ≥ 4`. -/
theorem norm_logDeriv_zetaChi_increment_le {τ : ℝ} {w : ℂ} (hτ : 4 ≤ |τ|)
    (hwim : 2 * |w.im| ≤ |τ|) (hwre₁ : -1 ≤ w.re) (hwre₂ : w.re ≤ 1) :
    ‖logDeriv zetaChi (linePt τ + w) - logDeriv zetaChi (linePt τ)‖ ≤ 10 * ‖w‖ / |τ| := by
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  have hseg : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      |τ| / 2 ≤ |(linePt τ + (θ : ℂ) * ((linePt τ + w) - linePt τ)).im| := by
    intro θ hθ
    have him : (linePt τ + (θ : ℂ) * ((linePt τ + w) - linePt τ)).im = τ + θ * w.im := by
      simp [linePt_im]
    rw [him]
    have h1 := abs_sub_abs_le_abs_sub τ (-(θ * w.im))
    have h2 : |θ * w.im| ≤ |w.im| := by
      rw [abs_mul, abs_of_nonneg hθ.1]
      exact mul_le_of_le_one_left (abs_nonneg _) hθ.2
    rw [sub_neg_eq_add, abs_neg] at h1
    linarith
  have hsegre : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      (linePt τ + (θ : ℂ) * ((linePt τ + w) - linePt τ)).re = 1 / 2 + θ * w.re := by
    intro θ _
    simp [linePt_re]
  have hM : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv (logDeriv zetaChi) (linePt τ + (θ : ℂ) * ((linePt τ + w) - linePt τ))‖
        ≤ 10 / |τ| := by
    intro θ hθ
    have hθ1 := hθ.1
    have hθ2 := hθ.2
    have hre₁ : -2 < (linePt τ + (θ : ℂ) * ((linePt τ + w) - linePt τ)).re := by
      rw [hsegre θ hθ]; nlinarith
    have hre₂ : (linePt τ + (θ : ℂ) * ((linePt τ + w) - linePt τ)).re < 3 := by
      rw [hsegre θ hθ]; nlinarith
    have him2 : 2 ≤ |(linePt τ + (θ : ℂ) * ((linePt τ + w) - linePt τ)).im| := by
      linarith [hseg θ hθ]
    have hb := norm_iteratedDeriv_logDeriv_zetaChi_le (n := 1) le_rfl hre₁ hre₂ him2
    rw [iteratedDeriv_one] at hb
    refine hb.trans ?_
    simp only [Nat.factorial_one, Nat.cast_one, mul_one, pow_one]
    rw [div_le_div_iff₀ (by linarith [hseg θ hθ]) hτ0]
    linarith [hseg θ hθ]
  have hdiff : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℂ (logDeriv zetaChi)
        (linePt τ + (θ : ℂ) * ((linePt τ + w) - linePt τ)) := by
    intro θ hθ
    have hmem : linePt τ + (θ : ℂ) * ((linePt τ + w) - linePt τ) ∈ offAxisSet := by
      show 1 < |(linePt τ + (θ : ℂ) * ((linePt τ + w) - linePt τ)).im|
      linarith [hseg θ hθ]
    exact (analyticOnNhd_logDeriv_zetaChi_offAxis _ hmem).differentiableAt
  have h := norm_sub_le_segment hdiff hM
  rw [add_sub_cancel_left] at h
  calc ‖logDeriv zetaChi (linePt τ + w) - logDeriv zetaChi (linePt τ)‖
      ≤ 10 / |τ| * ‖w‖ := h
    _ = 10 * ‖w‖ / |τ| := by ring

/-- **Increment bound**: for `t ≥ 4`, `2|Im w| ≤ t` and `|Re w| ≤ 1`,
`‖D_t(w)‖ ≤ 20‖w‖/t`. -/
theorem norm_critIncrement_le {t : ℝ} {w : ℂ} (ht : 4 ≤ t) (hwim : 2 * |w.im| ≤ t)
    (hwre₁ : -1 ≤ w.re) (hwre₂ : w.re ≤ 1) :
    ‖critIncrement t w‖ ≤ 20 * ‖w‖ / t := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have habs : |t| = t := abs_of_nonneg ht0
  have habs' : |-t| = t := by rw [abs_neg, habs]
  have h1 := norm_logDeriv_zetaChi_increment_le (τ := t) (w := w) (by rw [habs]; exact ht)
    (by rw [habs]; exact hwim) hwre₁ hwre₂
  have h2 := norm_logDeriv_zetaChi_increment_le (τ := -t) (w := w) (by rw [habs']; exact ht)
    (by rw [habs']; exact hwim) hwre₁ hwre₂
  rw [habs] at h1
  rw [habs'] at h2
  unfold critIncrement
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
  calc _ ≤ 10 * ‖w‖ / t + 10 * ‖w‖ / t := add_le_add h1 h2
    _ = 20 * ‖w‖ / t := by ring

/-! ## Size of the carrier -/

/-- On the dual contour `w = −(1+iv)`: `‖G_t‖ ≤ (1+|t|)²(1+|v|)²`. -/
theorem norm_critCarrier_dual_le (t v : ℝ) :
    ‖critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ (1 + |t|) ^ 2 * (1 + |v|) ^ 2 := by
  unfold critCarrier
  rw [norm_mul]
  have h1 := norm_smoothAFEZetaChiShiftRatio_neg_right_one_le t v
  have h2 := norm_smoothAFEZetaChiShiftRatio_neg_right_one_le (-t) v
  rw [abs_neg] at h2
  calc _ ≤ ((1 + |t|) * (1 + |v|)) * ((1 + |t|) * (1 + |v|)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = (1 + |t|) ^ 2 * (1 + |v|) ^ 2 := by ring

/-- The shifted argument of a right contour lies on the line `Re s = ½ + δ`. -/
theorem linePt_add_right_shift (τ δ v : ℝ) :
    linePt τ + (((δ : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I) =
      (((1 / 2 + δ : ℝ) : ℂ) + ((τ - v : ℝ) : ℂ) * I) := by
  unfold linePt
  push_cast
  ring

/-- On a right contour `w = δ − iv`: the carrier decays like the product of the two
`|χ|`-envelopes on `Re s = ½+δ`. -/
theorem exists_norm_critCarrier_right_le {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t v : ℝ,
      ‖critCarrier t (((δ : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I)‖ ≤
        K / ((max 1 |t - v|) ^ δ * (max 1 |-t - v|) ^ δ) := by
  obtain ⟨K, hK, hχ⟩ := exists_norm_zetaChi_fixed_right_line_le_rpow hδ hδhalf
  refine ⟨K * K, by positivity, fun t v => ?_⟩
  unfold critCarrier smoothAFEZetaChiShiftRatio
  rw [norm_mul, norm_div, norm_div, norm_zetaChi_line, norm_zetaChi_line, div_one, div_one,
    linePt_add_right_shift, linePt_add_right_shift]
  have h1 := hχ (t - v)
  have h2 := hχ (-t - v)
  have hp1 : 0 < (max 1 |t - v|) ^ δ := Real.rpow_pos_of_pos (by positivity) _
  have hp2 : 0 < (max 1 |-t - v|) ^ δ := Real.rpow_pos_of_pos (by positivity) _
  calc _ ≤ K / (max 1 |t - v|) ^ δ * (K / (max 1 |-t - v|) ^ δ) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = K * K / ((max 1 |t - v|) ^ δ * (max 1 |-t - v|) ^ δ) := by
        field_simp

/-! ## Nonvanishing on the two contours -/

theorem gammaR_one_sub_dual_ne_zero (τ v : ℝ) :
    Gammaℝ (1 - (linePt τ + -(((1 : ℝ) : ℂ) + (v : ℂ) * I))) ≠ 0 := by
  apply Gammaℝ_ne_zero_of_re_pos
  simp [linePt_re]
  norm_num

theorem zetaChi_dual_ne_zero (τ v : ℝ) :
    zetaChi (linePt τ + -(((1 : ℝ) : ℂ) + (v : ℂ) * I)) ≠ 0 := by
  simpa only [sub_eq_add_neg] using zetaChi_line_add_neg_right_one_ne_zero τ v

theorem gammaR_one_sub_right_ne_zero {δ : ℝ} (hδhalf : δ < 1 / 2) (τ v : ℝ) :
    Gammaℝ (1 - (linePt τ + (((δ : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I))) ≠ 0 := by
  apply Gammaℝ_ne_zero_of_re_pos
  rw [linePt_add_right_shift]
  simp
  linarith

theorem zetaChi_right_ne_zero {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (τ v : ℝ) :
    zetaChi (linePt τ + (((δ : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I)) ≠ 0 := by
  rw [linePt_add_right_shift]
  apply zetaChi_ne_zero_of_mem_openStrip
  · simp; linarith
  · simp; linarith

theorem hasDerivAt_critCarrier_dual (t v : ℝ) :
    HasDerivAt (fun s : ℝ => critCarrier s (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)))
      (critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        critIncrement t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) t :=
  hasDerivAt_critCarrier (gammaR_one_sub_dual_ne_zero t v) (zetaChi_dual_ne_zero t v)
    (gammaR_one_sub_dual_ne_zero (-t) v) (zetaChi_dual_ne_zero (-t) v)

theorem hasDerivAt_critCarrier_right {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (t v : ℝ) :
    HasDerivAt (fun s : ℝ => critCarrier s (((δ : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I))
      (critCarrier t (((δ : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I) *
        critIncrement t (((δ : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I)) t :=
  hasDerivAt_critCarrier (gammaR_one_sub_right_ne_zero hδhalf t v)
    (zetaChi_right_ne_zero hδ hδhalf t v) (gammaR_one_sub_right_ne_zero hδhalf (-t) v)
    (zetaChi_right_ne_zero hδ hδhalf (-t) v)

end RHTower.ZetaNotch
