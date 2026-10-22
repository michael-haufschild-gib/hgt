import GaloisForLFunctions.RHTower.PrimeAlmostAllShortIntervals

/-!
# The prime number theorem in almost all intervals `(x, x + X^{θ-1}x]`, `θ > 1/6`

For `1/6 < θ < 1`, `δ = X^{θ-1}` and `0 < ε ≤ 1`, the measure of the `x ∈ [X, 2X]` with
`|ψ(x + δx) - ψ(x) - δx| > ε δx` is `o(X)` (`tendsto_volume_psi_short_asymptotic`).

The lower squeeze is `psi_mul_window_ge`.  The upper squeeze uses the outer windows
`[x(1+δ), x(1+δ+η)]` and `[x(1-η), x]` (`psi_mul_window_le`): with
`e_ρ = T(ρ; 1+δ, 1+δ+η) - T(ρ; 1-η, 1)`,

`ψ(x + δx) - ψ(x) ≤ (δ + 2η)x + 4/(ηx²) + Re Σ_ρ x^ρ e_ρ`,

and `|e_ρ| ≤ 4(δ + 2η)`, `|e_ρ| ≤ 9/(η|ρ||1-ρ|)`.  With `η = εδ/16` both coefficient families obey
`|c_ρ|² ≤ 25δ² min(1, (192/(5ε))/(δ²|ρ||1-ρ|))`, so the mean square of each near sum is the zero
weight at `x = X²`, and Chebyshev's inequality (`volume_ge_norm_zeroSum_le`) finishes as in
`PrimeAlmostAllShortIntervals`.
-/

noncomputable section

namespace RHTower

open Complex Filter Topology MeasureTheory RHTower.Sieve

/-- **The `ψ` window upper bound, signed form.**  As `psi_window_le_add_tsum`, keeping the zero sum
inside the real part. -/
theorem psi_window_le_add_re_tsum {x h h' : ℝ} (hx : 4 ≤ x) (hh' : 0 < h') (hh'h : 2 * h' ≤ h)
    (hhx : h ≤ x / 2) :
    Chebyshev.psi (x + h) - Chebyshev.psi x ≤
      h + 2 * h' + 4 / (x * h')
        + (∑' q : XiZeroCopy, (lagWindowZeroTerm (q.1 : ℂ) (x + h) (x + h + h')
            - lagWindowZeroTerm (q.1 : ℂ) (x - h') x)).re := by
  set a₃ := x + h with ha₃
  set b₃ := x + h + h' with hb₃
  set a₄ := x - h' with ha₄
  have hx0 : 0 < x := by linarith
  have ha₃1 : 1 < a₃ := by rw [ha₃]; linarith
  have hab₃ : a₃ < b₃ := by rw [ha₃, hb₃]; linarith
  have ha₄1 : 1 < a₄ := by rw [ha₄]; linarith
  have hab₄ : a₄ < x := by rw [ha₄]; linarith
  have ha₃0 : 0 < a₃ := by linarith
  have ha₄0 : 0 < a₄ := by linarith
  have hw₃ : 0 < 1 / a₃ - 1 / b₃ := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha₃0 hab₃
  have hw₄ : 0 < 1 / a₄ - 1 / x := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha₄0 hab₄
  have hsq₃ := (chebyshevLagWindow_bounds ha₃0 hab₃.le).1
  have hsq₄ := (chebyshevLagWindow_bounds ha₄0 hab₄.le).2
  have hψ₃ : Chebyshev.psi a₃ ≤ chebyshevLagWindow a₃ b₃ / (1 / a₃ - 1 / b₃) := by
    rw [le_div_iff₀ hw₃]
    exact hsq₃
  have hψ₄ : chebyshevLagWindow a₄ x / (1 / a₄ - 1 / x) ≤ Chebyshev.psi x := by
    rw [div_le_iff₀ hw₄]
    exact hsq₄
  rw [chebyshevLagWindow_div_eq ha₃1 hab₃] at hψ₃
  rw [chebyshevLagWindow_div_eq ha₄1 hab₄] at hψ₄
  have hL₃ : Real.log (b₃ / a₃) / (1 / a₃ - 1 / b₃) ≤ b₃ := by
    rw [div_le_iff₀ hw₃]
    exact (log_div_le_mul_inv_sub ha₃0 hab₃.le).2
  have hL₄ : a₄ ≤ Real.log (x / a₄) / (1 / a₄ - 1 / x) := by
    rw [le_div_iff₀ hw₄]
    exact (log_div_le_mul_inv_sub ha₄0 hab₄.le).1
  have hE₄ : 0 ≤ (trivialZeroSeriesReal a₄ / a₄ - trivialZeroSeriesReal x / x)
      / (1 / a₄ - 1 / x) :=
    div_nonneg (sub_nonneg.mpr (trivialZeroSeriesReal_div_anti ha₄1.le hab₄.le)) hw₄.le
  have hE₃ : (trivialZeroSeriesReal a₃ / a₃ - trivialZeroSeriesReal b₃ / b₃)
      / (1 / a₃ - 1 / b₃) ≤ 4 / (x * h') := by
    have hEb := trivialZeroSeriesReal_nonneg (ha₃1.le.trans hab₃.le)
    have hEa := trivialZeroSeriesReal_le_two_div_sq (show 2 ≤ a₃ by rw [ha₃]; linarith)
    have hb₃0 : 0 < b₃ := by linarith
    have hnum : trivialZeroSeriesReal a₃ / a₃ - trivialZeroSeriesReal b₃ / b₃ ≤
        2 / a₃ ^ 2 / a₃ := by
      have : 0 ≤ trivialZeroSeriesReal b₃ / b₃ := div_nonneg hEb hb₃0.le
      have : trivialZeroSeriesReal a₃ / a₃ ≤ 2 / a₃ ^ 2 / a₃ :=
        div_le_div_of_nonneg_right hEa ha₃0.le
      linarith
    have hweq : 1 / a₃ - 1 / b₃ = h' / (a₃ * b₃) := by
      have hne1 : a₃ ≠ 0 := ha₃0.ne'
      have hne2 : b₃ ≠ 0 := hb₃0.ne'
      field_simp
      rw [hb₃, ha₃]
      ring
    rw [div_le_iff₀ hw₃, hweq]
    refine le_trans hnum ?_
    rw [show 4 / (x * h') * (h' / (a₃ * b₃)) = 4 / (x * (a₃ * b₃)) by field_simp, div_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have k1 : x * b₃ ≤ a₃ * (2 * a₃) :=
      mul_le_mul (by rw [ha₃]; linarith) (by rw [hb₃, ha₃]; linarith) (by linarith) (by linarith)
    nlinarith [k1, ha₃0]
  have hs₃ := summable_norm_lagWindowZeroTerm ha₃1.le hab₃
  have hs₄ := summable_norm_lagWindowZeroTerm ha₄1.le hab₄
  have hdiff : (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a₃ b₃).re
      - (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a₄ x).re
      = (∑' q : XiZeroCopy, (lagWindowZeroTerm (q.1 : ℂ) a₃ b₃
          - lagWindowZeroTerm (q.1 : ℂ) a₄ x)).re := by
    rw [← Complex.sub_re, ← (Summable.of_norm hs₃).tsum_sub (Summable.of_norm hs₄)]
  have hab : b₃ - a₄ = h + 2 * h' := by rw [hb₃, ha₄]; ring
  linarith

/-- The coefficient of `x^ρ` in the outer multiplicative two-window zero sum. -/
def multWindowCoeffOuter (δ η : ℝ) (ρ : ℂ) : ℂ :=
  lagWindowZeroTerm ρ (1 + δ) (1 + δ + η) - lagWindowZeroTerm ρ (1 - η) 1

/-- **The multiplicative window upper bound.**  For `4 ≤ x`, `0 < η`, `2η ≤ δ ≤ 1/2`:
`ψ(x + δx) - ψ(x) ≤ (δ + 2η)x + 4/(η x²) + Re Σ_ρ x^ρ e_ρ`. -/
theorem psi_mul_window_le {x δ η : ℝ} (hx : 4 ≤ x) (hη : 0 < η) (hηδ : 2 * η ≤ δ)
    (hδ : δ ≤ 1 / 2) :
    Chebyshev.psi (x + δ * x) - Chebyshev.psi x ≤
      (δ + 2 * η) * x + 4 / (η * x ^ 2)
        + (∑' q : XiZeroCopy, (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeffOuter δ η (q.1 : ℂ)).re := by
  have hx0 : 0 < x := by linarith
  have h := psi_window_le_add_re_tsum (h := δ * x) (h' := η * x) hx (by positivity)
    (by nlinarith) (by nlinarith)
  have hsum : (∑' q : XiZeroCopy, (lagWindowZeroTerm (q.1 : ℂ) (x + δ * x) (x + δ * x + η * x)
      - lagWindowZeroTerm (q.1 : ℂ) (x - η * x) x))
      = ∑' q : XiZeroCopy, (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeffOuter δ η (q.1 : ℂ) := by
    refine tsum_congr fun q => ?_
    have e1 : x + δ * x = (1 + δ) * x := by ring
    have e2 : x + δ * x + η * x = (1 + δ + η) * x := by ring
    have e3 : x - η * x = (1 - η) * x := by ring
    rw [e2, e1, e3]
    conv_lhs => rw [show lagWindowZeroTerm (q.1 : ℂ) ((1 - η) * x) x
      = lagWindowZeroTerm (q.1 : ℂ) ((1 - η) * x) (1 * x) by rw [one_mul]]
    rw [lagWindowZeroTerm_mul_scale hx0 (by linarith) (by linarith),
      lagWindowZeroTerm_mul_scale hx0 (by linarith) (by linarith), multWindowCoeffOuter, mul_sub]
  rw [hsum] at h
  have e5 : δ * x + 2 * (η * x) + 4 / (x * (η * x)) = (δ + 2 * η) * x + 4 / (η * x ^ 2) := by
    rw [show x * (η * x) = η * x ^ 2 by ring]
    ring
  linarith

/-- **Short range, outer windows.**  `|e_ρ| ≤ 4(δ + 2η)` for `η ≤ 1/2`. -/
theorem norm_multWindowCoeffOuter_le {δ η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hδ : 0 ≤ δ)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) : ‖multWindowCoeffOuter δ η ρ‖ ≤ 4 * (δ + 2 * η) := by
  have h := norm_lagWindowZeroTerm_sub_le (x := 1 - η) (H := δ + 2 * η) (a₁ := 1 + δ)
    (b₁ := 1 + δ + η) (a₂ := 1 - η) (b₂ := 1) (by linarith) (by linarith) (by linarith)
    (by linarith) le_rfl (by linarith) (by linarith) hρ0 hρ1
  have hp : (1 - η) ^ (ρ.re - 1) ≤ 2 := by
    calc (1 - η) ^ (ρ.re - 1) ≤ (1 / 2 : ℝ) ^ (ρ.re - 1) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
      _ ≤ (1 / 2 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = 2 := by norm_num
  calc ‖multWindowCoeffOuter δ η ρ‖ ≤ 2 * (δ + 2 * η) * (1 - η) ^ (ρ.re - 1) := h
    _ ≤ 2 * (δ + 2 * η) * 2 := by gcongr
    _ = 4 * (δ + 2 * η) := by ring

/-- **Long range, outer windows.**  `|e_ρ| ≤ 9/(η|ρ||1-ρ|)` for `0 < η ≤ 1/4`, `0 ≤ δ ≤ 1/2`. -/
theorem norm_multWindowCoeffOuter_le_div {δ η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 2) {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ‖multWindowCoeffOuter δ η ρ‖ ≤ 9 / (η * (‖ρ‖ * ‖1 - ρ‖)) := by
  have hρne : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hρ1ne : 1 - ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hP : 0 < ‖ρ‖ * ‖1 - ρ‖ := mul_pos (norm_pos_iff.mpr hρne) (norm_pos_iff.mpr hρ1ne)
  have hw₁ : η / 3 ≤ 1 / (1 + δ) - 1 / (1 + δ + η) := by
    have h1 : 0 < 1 + δ := by linarith
    have h2 : 0 < 1 + δ + η := by linarith
    have h3 : (1 + δ) * (1 + δ + η) ≤ 3 := by nlinarith
    rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h3 hη.le]
  have hT₁ := norm_lagWindowZeroTerm_le_of_width (a := 1 + δ) (b := 1 + δ + η) (by linarith)
    (by linarith) (by positivity) hw₁ hρ0 hρ1
  have hT₂ := norm_lagWindowZeroTerm_le (a := 1 - η) (b := 1) (by linarith) (by linarith) ρ
  have hp : (1 - η) ^ (ρ.re - 1) ≤ 2 := by
    calc (1 - η) ^ (ρ.re - 1) ≤ (1 / 2 : ℝ) ^ (ρ.re - 1) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
      _ ≤ (1 / 2 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = 2 := by norm_num
  have hw₂ : η ≤ 1 / (1 - η) - 1 / 1 := by
    have h1 : 0 < 1 - η := by linarith
    rw [div_one, div_sub_one h1.ne', le_div_iff₀ h1]
    nlinarith
  have hT₂' : ‖lagWindowZeroTerm ρ (1 - η) 1‖ ≤ 3 / (η * (‖ρ‖ * ‖1 - ρ‖)) := by
    refine le_trans hT₂ ?_
    rw [Real.one_rpow]
    calc ((1 - η) ^ (ρ.re - 1) + 1) / (‖ρ‖ * ‖1 - ρ‖ * (1 / (1 - η) - 1 / 1))
        ≤ 3 / (‖ρ‖ * ‖1 - ρ‖ * (1 / (1 - η) - 1 / 1)) :=
          div_le_div_of_nonneg_right (by linarith) (mul_pos hP (by linarith)).le
      _ ≤ 3 / (‖ρ‖ * ‖1 - ρ‖ * η) := by gcongr
      _ = 3 / (η * (‖ρ‖ * ‖1 - ρ‖)) := by ring_nf
  have e₁ : 2 / (‖ρ‖ * ‖1 - ρ‖ * (η / 3)) = 6 / (η * (‖ρ‖ * ‖1 - ρ‖)) := by
    field_simp
    ring
  rw [e₁] at hT₁
  have e₃ : 9 / (η * (‖ρ‖ * ‖1 - ρ‖))
      = 6 / (η * (‖ρ‖ * ‖1 - ρ‖)) + 3 / (η * (‖ρ‖ * ‖1 - ρ‖)) := by ring
  rw [multWindowCoeffOuter, e₃]
  exact le_trans (norm_sub_le _ _) (add_le_add hT₁ hT₂')

/-- `|c|² ≤ a² min(1, (b/a)/P)` from `|c| ≤ a` and `|c| ≤ b/P`. -/
theorem sq_le_mul_min_of_le {c a b P : ℝ} (hc0 : 0 ≤ c) (ha : 0 < a) (hP : 0 < P)
    (hca : c ≤ a) (hcb : c ≤ b / P) : c ^ 2 ≤ a ^ 2 * min 1 (b / a / P) := by
  rcases le_total 1 (b / a / P) with h | h
  · rw [min_eq_left h, mul_one]
    exact pow_le_pow_left₀ hc0 hca 2
  · rw [min_eq_right h]
    calc c ^ 2 = c * c := sq c
      _ ≤ a * (b / P) := mul_le_mul hca hcb hc0 ha.le
      _ = a ^ 2 * (b / a / P) := by field_simp

/-- **Chebyshev's inequality for a finite zero sum on `[X, 2X]`.** -/
theorem volume_ge_norm_zeroSum_le {X r W : ℝ} (hX : 0 < X) (hr : 0 < r) (F : Finset XiZeroCopy)
    (c : XiZeroCopy → ℂ)
    (hW : ∀ q ∈ F, ∑ q' ∈ F, 1 / (1 + |(q.1 : ℂ).im - (q'.1 : ℂ).im|) ≤ W) :
    (volume {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ r ≤ ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖}).toReal
      ≤ (2 * X) ^ 3 / r ^ 2 * (4 * W * ∑ q ∈ F, ‖c q‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)) := by
  set g : ℝ → ℝ := fun x => ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 with hg
  set κ : ℝ := r ^ 2 / (2 * X) ^ 3 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hsub : {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ r ≤ ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖}
      ⊆ {x : ℝ | κ ≤ g x} ∩ Set.Icc X (2 * X) := by
    rintro x ⟨hx, hle⟩
    refine ⟨?_, hx⟩
    have hx0 : 0 < x := by linarith [hx.1]
    have hn2 : r ^ 2 ≤ ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 :=
      pow_le_pow_left₀ hr.le hle 2
    have hx3 : x ^ 3 ≤ (2 * X) ^ 3 := by
      have := hx.2
      gcongr
    show κ ≤ ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3
    rw [hκ]
    calc r ^ 2 / (2 * X) ^ 3 ≤ r ^ 2 / x ^ 3 := by gcongr
      _ ≤ ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 := by gcongr
  have hX2 : X ≤ 2 * X := by linarith
  have hcontD : ContinuousOn (fun x : ℝ => ∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ))
      (Set.Icc X (2 * X)) := by
    refine continuousOn_finsetSum _ fun q _ => continuousOn_const.mul ?_
    refine continuousOn_of_forall_continuousAt fun x hx => ?_
    exact Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (by linarith [hx.1]))
  have hcontg : ContinuousOn g (Set.Icc X (2 * X)) := by
    refine (hcontD.norm.pow 2).div (continuousOn_pow 3) fun x hx => ?_
    have : 0 < x := by linarith [hx.1]
    positivity
  have hgint : Integrable g (volume.restrict (Set.Icc X (2 * X))) := hcontg.integrableOn_Icc
  have hg0 : 0 ≤ᵐ[volume.restrict (Set.Icc X (2 * X))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have : 0 < x := by linarith [hx.1]
    simp only [Pi.zero_apply, hg]
    positivity
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hg0 hgint κ
  rw [measureReal_def, Measure.restrict_apply' measurableSet_Icc] at hmarkov
  have hint_eq : ∫ x, g x ∂(volume.restrict (Set.Icc X (2 * X))) = ∫ x in X..2 * X, g x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hX2]
  rw [hint_eq] at hmarkov
  have hms := integral_norm_sq_zeroSum_div_cube_le hX F c hW
  have hvol : (volume {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ r ≤ ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖}).toReal
      ≤ (volume ({x : ℝ | κ ≤ g x} ∩ Set.Icc X (2 * X))).toReal := by
    refine ENNReal.toReal_mono ?_ (measure_mono hsub)
    refine ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  refine le_trans hvol ?_
  rw [hκ] at hmarkov
  have hm := le_trans hmarkov hms
  have hpos : 0 < r ^ 2 / (2 * X) ^ 3 := by positivity
  rw [show (2 * X) ^ 3 / r ^ 2 * (4 * W * ∑ q ∈ F, ‖c q‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2))
    = (4 * W * ∑ q ∈ F, ‖c q‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)) / (r ^ 2 / (2 * X) ^ 3) by
      field_simp]
  rw [le_div_iff₀ hpos]
  linarith

/-- **Far zeros, general coefficients.**  If `|f(ρ)| ≤ K/(|ρ||1-ρ|)` on the zeros, `1 ≤ x` and
`1 ≤ T`, the zeros of ordinate above `T` contribute at most `3Kx/√T · Σ_ρ |ρ-½|^{-3/2}`. -/
theorem norm_tsum_compl_le_of_bound {x T K : ℝ} (hx : 1 ≤ x) (hT : 1 ≤ T) (hK : 0 ≤ K)
    (f : ℂ → ℂ) (hf : ∀ q : XiZeroCopy, ‖f (q.1 : ℂ)‖ ≤ K / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) :
    ‖∑' q : ↑(((finite_xiOrdinateWindow T 0).toFinset : Finset XiZeroCopy) : Set XiZeroCopy)ᶜ,
        (x : ℂ) ^ ((q : XiZeroCopy).1 : ℂ) * f ((q : XiZeroCopy).1 : ℂ)‖
      ≤ 3 * K * x / Real.sqrt T * xiSpectralThreeHalvesMass := by
  set F : Finset XiZeroCopy := (finite_xiOrdinateWindow T 0).toFinset with hF
  set S : XiZeroCopy → ℝ := fun q => 1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)
    with hS
  have hSs : Summable S := xiSpectralPoint_inv_three_halves_summable
  have hS0 : ∀ q, 0 ≤ S q := fun q => by rw [hS]; positivity
  have hx0 : 0 < x := by linarith
  have hsT0 : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
  set M : ℝ := 3 * K * x / Real.sqrt T with hM
  have hpt : ∀ q : XiZeroCopy, q ∉ F → ‖(x : ℂ) ^ (q.1 : ℂ) * f (q.1 : ℂ)‖ ≤ M * S q := by
    intro q hq
    have hγ : T < |(q.1 : ℂ).im| := by
      rw [hF, Set.Finite.mem_toFinset, mem_xiOrdinateWindow_iff, sub_zero] at hq
      exact lt_of_not_ge hq
    have hρ1 := xiZeroCopy_re_lt_one q
    have hP : (q.1 : ℂ).im ^ 2 ≤ ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ := by
      have h1 := Complex.abs_im_le_norm (q.1 : ℂ)
      have h2 := Complex.abs_im_le_norm (1 - (q.1 : ℂ))
      have h3 : |(1 - (q.1 : ℂ)).im| = |(q.1 : ℂ).im| := by simp
      rw [h3] at h2
      rw [← sq_abs]
      nlinarith [abs_nonneg (q.1 : ℂ).im]
    have hγ1 : 1 < |(q.1 : ℂ).im| := lt_of_le_of_lt hT hγ
    have hγ2 : 0 < (q.1 : ℂ).im ^ 2 := by
      rw [← sq_abs]
      positivity
    have hxp : ‖(x : ℂ) ^ (q.1 : ℂ)‖ ≤ x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      exact Real.rpow_le_self_of_one_le hx hρ1.le
    have hsp := inv_sq_im_le_spectral hT hγ
    rw [norm_mul]
    calc ‖(x : ℂ) ^ (q.1 : ℂ)‖ * ‖f (q.1 : ℂ)‖ ≤ x * (K / (q.1 : ℂ).im ^ 2) := by
          gcongr
          refine le_trans (hf q) ?_
          gcongr
      _ = K * x * (1 / (q.1 : ℂ).im ^ 2) := by field_simp
      _ ≤ K * x * (3 / Real.sqrt T * S q) := by gcongr
      _ = M * S q := by rw [hM]; field_simp
  set g : XiZeroCopy → ℂ := fun q => (x : ℂ) ^ (q.1 : ℂ) * f (q.1 : ℂ) with hg
  have hsub : ∑' q : ↑((F : Set XiZeroCopy)ᶜ), g q = ∑' q, ((F : Set XiZeroCopy)ᶜ).indicator g q :=
    tsum_subtype _ g
  have hind : ∀ q : XiZeroCopy, ‖((F : Set XiZeroCopy)ᶜ).indicator g q‖ ≤ M * S q := by
    intro q
    by_cases hq : q ∈ F
    · rw [Set.indicator_of_notMem (by simpa using hq), norm_zero]
      exact mul_nonneg (by positivity) (hS0 q)
    · rw [Set.indicator_of_mem (by simpa using hq)]
      exact hpt q hq
  have hsumnorm : Summable fun q => ‖((F : Set XiZeroCopy)ᶜ).indicator g q‖ :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) hind (hSs.mul_left M)
  change ‖∑' q : ↑((F : Set XiZeroCopy)ᶜ), g q‖ ≤ _
  rw [hsub]
  refine le_trans (norm_tsum_le_tsum_norm hsumnorm) ?_
  rw [xiSpectralThreeHalvesMass, ← tsum_mul_left]
  exact Summable.tsum_le_tsum hind hsumnorm (hSs.mul_left M)

/-- The harmonic weight of the zeros of ordinate at most `X⁴`. -/
theorem sum_inv_lowZeros_le_harmonicWeight {X : ℝ} (hX1 : 1 ≤ X) :
    ∀ q ∈ almostAllLowZeros X, ∑ q' ∈ almostAllLowZeros X,
      1 / (1 + |(q.1 : ℂ).im - (q'.1 : ℂ).im|) ≤ almostAllHarmonicWeight X := by
  intro q hq
  set F := almostAllLowZeros X with hF
  have hmem : ∀ q' ∈ F, |(q'.1 : ℂ).im| ≤ X ^ 4 := by
    intro q' hq'
    rw [hF, almostAllLowZeros, Set.Finite.mem_toFinset, mem_xiOrdinateWindow_iff,
      sub_zero] at hq'
    exact hq'
  have hq4 := hmem q hq
  have hR : ∀ q' ∈ F, |(q'.1 : ℂ).im - (q.1 : ℂ).im| ≤ 2 * X ^ 4 := by
    intro q' hq'
    have := hmem q' hq'
    have := abs_sub (q'.1 : ℂ).im (q.1 : ℂ).im
    linarith
  have hharm := sum_inv_one_add_abs_im_sub_le F (t := (q.1 : ℂ).im) (by positivity) hR
  have hcomm : ∑ q' ∈ F, 1 / (1 + |(q.1 : ℂ).im - (q'.1 : ℂ).im|)
      = ∑ q' ∈ F, 1 / (1 + |(q'.1 : ℂ).im - (q.1 : ℂ).im|) := by
    refine Finset.sum_congr rfl fun q' _ => ?_
    rw [abs_sub_comm]
  rw [hcomm]
  refine le_trans hharm ?_
  rw [almostAllHarmonicWeight]
  have hX4 : 1 ≤ X ^ 4 := one_le_pow₀ hX1
  have hl : Real.log (|(q.1 : ℂ).im| + 2 * X ^ 4 + 4) ≤ Real.log (3 * X ^ 4 + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hl0 : 0 ≤ 1 + Real.log (2 * X ^ 4 + 1) := by
    have : 0 ≤ Real.log (2 * X ^ 4 + 1) := Real.log_nonneg (by linarith)
    linarith
  gcongr

/-- The inner near sum `Σ_{|γ| ≤ X⁴} d_ρ x^ρ` at a free window ratio `δ`, `η = εδ/16`. -/
def asymInnerSumAt (δ ε X x : ℝ) : ℂ :=
  ∑ q ∈ almostAllLowZeros X, multWindowCoeff δ (ε * δ / 16) (q.1 : ℂ) * (x : ℂ) ^ (q.1 : ℂ)

/-- The outer near sum at a free window ratio `δ`. -/
def asymOuterSumAt (δ ε X x : ℝ) : ℂ :=
  ∑ q ∈ almostAllLowZeros X, multWindowCoeffOuter δ (ε * δ / 16) (q.1 : ℂ) * (x : ℂ) ^ (q.1 : ℂ)

/-- The inner near sum `Σ_{|γ| ≤ X⁴} d_ρ x^ρ` at `δ = X^{θ-1}`, `η = εδ/16`. -/
def asymInnerSum (θ ε X x : ℝ) : ℂ := asymInnerSumAt (X ^ (θ - 1)) ε X x

/-- The outer near sum `Σ_{|γ| ≤ X⁴} e_ρ x^ρ` at `δ = X^{θ-1}`, `η = εδ/16`. -/
def asymOuterSum (θ ε X x : ℝ) : ℂ := asymOuterSumAt (X ^ (θ - 1)) ε X x

/-- **The two-sided pointwise bound.**  For `x ∈ [X, 2X]`, `δ = X^{θ-1} ≤ 1/2` and
`16(64 + 1152 Σ) ≤ ε² X^{2θ}`: `|ψ(x + δx) - ψ(x) - δx| ≤ (3ε/16)δx + |D(x)| + |E(x)|`. -/
theorem abs_psi_short_sub_le_at {δ ε X x : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 4 ≤ X)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * (δ * X) ^ 2)
    (hx : x ∈ Set.Icc X (2 * X)) :
    |Chebyshev.psi (x + δ * x) - Chebyshev.psi x - δ * x|
      ≤ 3 * ε / 16 * (δ * x) + ‖asymInnerSumAt δ ε X x‖ + ‖asymOuterSumAt δ ε X x‖ := by
  set η := ε * δ / 16 with hηdef
  set Ms := xiSpectralThreeHalvesMass with hMs
  have hMs0 : 0 ≤ Ms := xiSpectralThreeHalvesMass_nonneg
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hx0 : 0 < x := by linarith [hx.1]
  have hx4 : 4 ≤ x := le_trans hX hx.1
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have h2η : 2 * η ≤ δ := by rw [hηdef]; nlinarith
  have hη4 : η ≤ 1 / 4 := by rw [hηdef]; nlinarith
  set F := almostAllLowZeros X with hF
  have hsq : Real.sqrt (X ^ 4) = X ^ 2 := by
    rw [show X ^ 4 = (X ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  -- the far parts
  have htailD := norm_tsum_compl_le_of_bound (x := x) (T := X ^ 4) (K := 12 / η) (by linarith)
    (one_le_pow₀ hX1) (by positivity) (multWindowCoeff δ η) (fun q => by
      have h := norm_multWindowCoeff_le_div hη0 h2η (by linarith) (xiZeroCopy_re_pos q)
        (xiZeroCopy_re_lt_one q)
      refine le_trans h (le_of_eq ?_)
      field_simp)
  have htailE := norm_tsum_compl_le_of_bound (x := x) (T := X ^ 4) (K := 9 / η) (by linarith)
    (one_le_pow₀ hX1) (by positivity) (multWindowCoeffOuter δ η) (fun q => by
      have h := norm_multWindowCoeffOuter_le_div hη0 hη4 hδ0.le hδ (xiZeroCopy_re_pos q)
        (xiZeroCopy_re_lt_one q)
      refine le_trans h (le_of_eq ?_)
      field_simp)
  rw [hsq] at htailD htailE
  set tD := ∑' q : ↑(((finite_xiOrdinateWindow (X ^ 4) 0).toFinset : Finset XiZeroCopy)
      : Set XiZeroCopy)ᶜ, (x : ℂ) ^ ((q : XiZeroCopy).1 : ℂ)
        * multWindowCoeff δ η ((q : XiZeroCopy).1 : ℂ) with htD
  set tE := ∑' q : ↑(((finite_xiOrdinateWindow (X ^ 4) 0).toFinset : Finset XiZeroCopy)
      : Set XiZeroCopy)ᶜ, (x : ℂ) ^ ((q : XiZeroCopy).1 : ℂ)
        * multWindowCoeffOuter δ η ((q : XiZeroCopy).1 : ℂ) with htE
  have hxX : x ≤ 2 * X := hx.2
  have hsmall_tail : ∀ K : ℝ, 0 ≤ K → K ≤ 12 →
      3 * (K / η) * x / X ^ 2 * Ms ≤ 72 * Ms / (η * X) := by
    intro K hK0 hK
    have e : 3 * (K / η) * x / X ^ 2 * Ms = (3 * K * x * Ms) / (η * X ^ 2) := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 3 * K * x * Ms ≤ 3 * 12 * (2 * X) * Ms := by gcongr
    calc 3 * K * x * Ms * (η * X) ≤ 3 * 12 * (2 * X) * Ms * (η * X) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 72 * Ms * (η * X ^ 2) := by ring
  have htD' : ‖tD‖ ≤ 72 * Ms / (η * X) := le_trans htailD (hsmall_tail 12 (by norm_num) le_rfl)
  have htE' : ‖tE‖ ≤ 72 * Ms / (η * X) := le_trans htailE (hsmall_tail 9 (by norm_num)
    (by norm_num))
  -- the summable zero sums and their splits
  have hsD : Summable fun q : XiZeroCopy =>
      (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeff δ η (q.1 : ℂ) := by
    refine Summable.of_norm_bounded (summable_norm_inv_mul_one_sub.mul_left (12 * x / η))
      fun q => ?_
    have hd := norm_multWindowCoeff_le_div hη0 h2η (by linarith) (xiZeroCopy_re_pos q)
      (xiZeroCopy_re_lt_one q)
    have hxp : ‖(x : ℂ) ^ (q.1 : ℂ)‖ ≤ x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      exact Real.rpow_le_self_of_one_le (by linarith) (xiZeroCopy_re_lt_one q).le
    rw [norm_inv_mul_one_sub_eq, norm_mul]
    calc ‖(x : ℂ) ^ (q.1 : ℂ)‖ * ‖multWindowCoeff δ η (q.1 : ℂ)‖
        ≤ x * (12 / (η * (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖))) := by gcongr
      _ = 12 * x / η * (1 / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) := by field_simp
  have hsE : Summable fun q : XiZeroCopy =>
      (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeffOuter δ η (q.1 : ℂ) := by
    refine Summable.of_norm_bounded (summable_norm_inv_mul_one_sub.mul_left (9 * x / η))
      fun q => ?_
    have hd := norm_multWindowCoeffOuter_le_div hη0 hη4 hδ0.le hδ (xiZeroCopy_re_pos q)
      (xiZeroCopy_re_lt_one q)
    have hxp : ‖(x : ℂ) ^ (q.1 : ℂ)‖ ≤ x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      exact Real.rpow_le_self_of_one_le (by linarith) (xiZeroCopy_re_lt_one q).le
    rw [norm_inv_mul_one_sub_eq, norm_mul]
    calc ‖(x : ℂ) ^ (q.1 : ℂ)‖ * ‖multWindowCoeffOuter δ η (q.1 : ℂ)‖
        ≤ x * (9 / (η * (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖))) := by gcongr
      _ = 9 * x / η * (1 / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) := by field_simp
  have hspD := hsD.sum_add_tsum_compl (s := F)
  have hspE := hsE.sum_add_tsum_compl (s := F)
  have hinD : ∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeff δ η (q.1 : ℂ)
      = asymInnerSumAt δ ε X x := by
    rw [asymInnerSumAt]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  have hinE : ∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeffOuter δ η (q.1 : ℂ)
      = asymOuterSumAt δ ε X x := by
    rw [asymOuterSumAt]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  have hreD : -‖asymInnerSumAt δ ε X x‖ - ‖tD‖ ≤
      (∑' q : XiZeroCopy, (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeff δ η (q.1 : ℂ)).re := by
    rw [← hspD, Complex.add_re, ← hinD]
    have h1 := Complex.abs_re_le_norm (∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeff δ η (q.1 : ℂ))
    have h2 := Complex.abs_re_le_norm tD
    have h3 := neg_abs_le (∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeff δ η (q.1 : ℂ)).re
    have h4 := neg_abs_le tD.re
    have : (∑' q : ↑((F : Set XiZeroCopy)ᶜ), (x : ℂ) ^ ((q : XiZeroCopy).1 : ℂ)
        * multWindowCoeff δ η ((q : XiZeroCopy).1 : ℂ)) = tD := rfl
    rw [this]
    linarith
  have hreE : (∑' q : XiZeroCopy, (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeffOuter δ η (q.1 : ℂ)).re
      ≤ ‖asymOuterSumAt δ ε X x‖ + ‖tE‖ := by
    rw [← hspE, Complex.add_re, ← hinE]
    have h1 := Complex.abs_re_le_norm
      (∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeffOuter δ η (q.1 : ℂ))
    have h2 := Complex.abs_re_le_norm tE
    have h3 := le_abs_self
      (∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeffOuter δ η (q.1 : ℂ)).re
    have h4 := le_abs_self tE.re
    have : (∑' q : ↑((F : Set XiZeroCopy)ᶜ), (x : ℂ) ^ ((q : XiZeroCopy).1 : ℂ)
        * multWindowCoeffOuter δ η ((q : XiZeroCopy).1 : ℂ)) = tE := rfl
    rw [this]
    linarith
  -- the squeezes
  have hlow := psi_mul_window_ge (by linarith : 2 ≤ x) hη0 h2η (by linarith : δ ≤ 1)
  have hup := psi_mul_window_le hx4 hη0 h2η hδ
  -- the small terms
  have htriv : 4 / (η * x ^ 2) ≤ 4 / (η * X ^ 2) := by
    have : X ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hX0.le hx.1 2
    gcongr
  have hsmall : 4 / (η * X ^ 2) + 72 * Ms / (η * X) ≤ ε / 16 * (δ * X) := by
    have e1 : 4 / (η * X ^ 2) + 72 * Ms / (η * X) = (4 / X + 72 * Ms) / (η * X) := by
      field_simp
    have e2 : η * X = ε * (δ * X) / 16 := by rw [hηdef]; ring
    rw [e1, e2, div_le_iff₀ (by positivity)]
    have h4X : 4 / X ≤ 4 := by rw [div_le_iff₀ hX0]; linarith
    have key : 16 * (4 + 72 * Ms) * 16 ≤ ε ^ 2 * (δ * X) ^ 2 := by linarith
    calc 4 / X + 72 * Ms ≤ 4 + 72 * Ms := by linarith
      _ ≤ ε / 16 * (δ * X) * (ε * (δ * X) / 16) := by
          have e3 : ε / 16 * (δ * X) * (ε * (δ * X) / 16) = ε ^ 2 * (δ * X) ^ 2 / 256 := by ring
          rw [e3]
          linarith
  have hηx : 2 * η * x = ε / 8 * (δ * x) := by rw [hηdef]; ring
  have hXx : ε / 16 * (δ * X) ≤ ε / 16 * (δ * x) := by
    have := mul_le_mul_of_nonneg_left hx.1 hδ0.le
    exact mul_le_mul_of_nonneg_left this (by positivity)
  rw [abs_le]
  constructor
  · -- lower side
    have h1 : (δ - 2 * η) * x = δ * x - 2 * η * x := by ring
    have hE0 := norm_nonneg (asymOuterSumAt δ ε X x)
    linarith
  · -- upper side
    have h1 : (δ + 2 * η) * x = δ * x + 2 * η * x := by ring
    have hD0 := norm_nonneg (asymInnerSumAt δ ε X x)
    linarith


/-- **The two-sided pointwise bound at `δ = X^{θ-1}`.** -/
theorem abs_psi_short_sub_le {θ ε X x : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 4 ≤ X)
    (hδ : X ^ (θ - 1) ≤ 1 / 2)
    (hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * X ^ (2 * θ))
    (hx : x ∈ Set.Icc X (2 * X)) :
    |Chebyshev.psi (x + X ^ (θ - 1) * x) - Chebyshev.psi x - X ^ (θ - 1) * x|
      ≤ 3 * ε / 16 * (X ^ (θ - 1) * x) + ‖asymInnerSum θ ε X x‖ + ‖asymOuterSum θ ε X x‖ := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hδX : X ^ (θ - 1) * X = X ^ θ := by
    rw [← Real.rpow_add_one hX0.ne']
    ring_nf
  have hsq2 : (X ^ θ) ^ 2 = X ^ (2 * θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
    ring_nf
  have hbig' : 16 * (64 + 1152 * xiSpectralThreeHalvesMass)
      ≤ ε ^ 2 * (X ^ (θ - 1) * X) ^ 2 := by rw [hδX, hsq2]; exact hbig
  exact abs_psi_short_sub_le_at hε hε1 hX (by positivity) hδ hbig' hx

/-- The coefficient bound shared by the inner and outer sums:
`|c_ρ|² X^{2β-2} ≤ 25δ² · zeroShortWeight(X², (192/(5ε))(X²)^{1-θ}, ρ)` whenever `|c_ρ| ≤ 5δ` and
`|c_ρ| ≤ 12/(η|ρ||1-ρ|)`, `δ = X^{θ-1}`, `η = εδ/16`. -/
theorem sq_norm_mul_rpow_le_zeroShortWeight {θ ε X : ℝ} (hε : 0 < ε) (hX : 0 < X) {c : ℂ}
    {q : XiZeroCopy} (hc5 : ‖c‖ ≤ 5 * X ^ (θ - 1))
    (hc12 : ‖c‖ ≤ 12 / (ε * X ^ (θ - 1) / 16 * (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖))) :
    ‖c‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)
      ≤ 25 * (X ^ (θ - 1)) ^ 2 * zeroShortWeight (X ^ 2)
          (192 / (5 * ε) * (X ^ 2) ^ (2 * ((1 - θ) / 2))) (q.1 : ℂ) := by
  set δ := X ^ (θ - 1) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hρne := xiZeroCopy_ne_zero q
  have hρ1ne : 1 - (q.1 : ℂ) ≠ 0 := xiZeroCopy_one_sub_ne_zero q
  set P := ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ with hP
  have hP0 : 0 < P := mul_pos (norm_pos_iff.mpr hρne) (norm_pos_iff.mpr hρ1ne)
  have hc12' : ‖c‖ ≤ (192 / (ε * δ)) / P := by
    refine le_trans hc12 (le_of_eq ?_)
    field_simp
    ring
  have hsq := sq_le_mul_min_of_le (norm_nonneg c) (by positivity : 0 < 5 * δ) hP0 hc5 hc12'
  have hY : 192 / (ε * δ) / (5 * δ) = 192 / (5 * ε) * (X ^ 2) ^ (2 * ((1 - θ) / 2)) := by
    have hX2 : (X ^ 2) ^ (2 * ((1 - θ) / 2)) = 1 / δ ^ 2 := by
      rw [hδdef, ← Real.rpow_natCast X 2, ← Real.rpow_mul hX.le,
        ← Real.rpow_natCast (X ^ (θ - 1)) 2, ← Real.rpow_mul hX.le, one_div,
        ← Real.rpow_neg hX.le]
      congr 1
      push_cast
      ring
    rw [hX2]
    field_simp
  rw [hY] at hsq
  have hXp : X ^ (2 * (q.1 : ℂ).re - 2) = (X ^ 2) ^ ((q.1 : ℂ).re - 1) := by
    rw [← Real.rpow_natCast X 2, ← Real.rpow_mul hX.le]
    congr 1
    push_cast
    ring
  rw [zeroShortWeight, hXp]
  have hXp0 : 0 ≤ (X ^ 2) ^ ((q.1 : ℂ).re - 1) := Real.rpow_nonneg (by positivity) _
  calc ‖c‖ ^ 2 * (X ^ 2) ^ ((q.1 : ℂ).re - 1)
      ≤ (5 * δ) ^ 2 * min 1 (192 / (5 * ε) * (X ^ 2) ^ (2 * ((1 - θ) / 2)) / P)
          * (X ^ 2) ^ ((q.1 : ℂ).re - 1) := by gcongr
    _ = 25 * δ ^ 2 * ((X ^ 2) ^ ((q.1 : ℂ).re - 1)
          * min 1 (192 / (5 * ε) * (X ^ 2) ^ (2 * ((1 - θ) / 2)) / P)) := by ring

/-- **Chebyshev's inequality for the asymptotic.** -/
theorem volume_psi_short_asymptotic_le {θ ε X : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 4 ≤ X)
    (hδ : X ^ (θ - 1) ≤ 1 / 2)
    (hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * X ^ (2 * θ)) :
    (volume {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ ε * (X ^ (θ - 1) * x)
        < |Chebyshev.psi (x + X ^ (θ - 1) * x) - Chebyshev.psi x - X ^ (θ - 1) * x|}).toReal
      ≤ 25600 / ε ^ 2 * almostAllHarmonicWeight X * X
        * ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2)
            (192 / (5 * ε) * (X ^ 2) ^ (2 * ((1 - θ) / 2))) (q.1 : ℂ) := by
  set δ := X ^ (θ - 1) with hδdef
  set η := ε * δ / 16 with hηdef
  set F := almostAllLowZeros X with hF
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have h2η : 2 * η ≤ δ := by rw [hηdef]; nlinarith
  have hη4 : η ≤ 1 / 4 := by rw [hηdef]; nlinarith
  have hη16 : η ≤ δ / 16 := by rw [hηdef]; nlinarith
  set r : ℝ := ε / 4 * (δ * X) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  set Y : ℝ := 192 / (5 * ε) * (X ^ 2) ^ (2 * ((1 - θ) / 2)) with hYdef
  set Z := ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2) Y (q.1 : ℂ) with hZ
  set W := almostAllHarmonicWeight X with hWdef
  have hW := sum_inv_lowZeros_le_harmonicWeight hX1
  have hW0 : 0 ≤ W := by
    rw [hWdef, almostAllHarmonicWeight]
    have hX4 : 1 ≤ X ^ 4 := one_le_pow₀ hX1
    have h1 : 0 ≤ Real.log (3 * X ^ 4 + 4) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log (2 * X ^ 4 + 1) := Real.log_nonneg (by linarith)
    positivity
  have hY0 : 0 ≤ Y := by rw [hYdef]; positivity
  have hZsum : Summable fun q : XiZeroCopy => zeroShortWeight (X ^ 2) Y (q.1 : ℂ) :=
    summable_zeroShortWeight (one_le_pow₀ hX1) hY0
  have hFZ : ∑ q ∈ F, zeroShortWeight (X ^ 2) Y (q.1 : ℂ) ≤ Z :=
    Summable.sum_le_tsum F (fun q _ => zeroShortWeight_nonneg (by positivity) hY0 _) hZsum
  -- the coefficient sums
  have hcoefD : ∑ q ∈ F, ‖multWindowCoeff δ η (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)
      ≤ 25 * δ ^ 2 * Z := by
    calc ∑ q ∈ F, ‖multWindowCoeff δ η (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)
        ≤ ∑ q ∈ F, 25 * δ ^ 2 * zeroShortWeight (X ^ 2) Y (q.1 : ℂ) := by
          refine Finset.sum_le_sum fun q _ => ?_
          refine sq_norm_mul_rpow_le_zeroShortWeight hε hX0 ?_ ?_
          · have := norm_multWindowCoeff_le_two_mul hη0 h2η (xiZeroCopy_re_pos q)
              (xiZeroCopy_re_lt_one q)
            linarith
          · exact norm_multWindowCoeff_le_div hη0 h2η (by linarith) (xiZeroCopy_re_pos q)
              (xiZeroCopy_re_lt_one q)
      _ = 25 * δ ^ 2 * ∑ q ∈ F, zeroShortWeight (X ^ 2) Y (q.1 : ℂ) := by rw [Finset.mul_sum]
      _ ≤ 25 * δ ^ 2 * Z := by gcongr
  have hcoefE : ∑ q ∈ F, ‖multWindowCoeffOuter δ η (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)
      ≤ 25 * δ ^ 2 * Z := by
    calc ∑ q ∈ F, ‖multWindowCoeffOuter δ η (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)
        ≤ ∑ q ∈ F, 25 * δ ^ 2 * zeroShortWeight (X ^ 2) Y (q.1 : ℂ) := by
          refine Finset.sum_le_sum fun q _ => ?_
          refine sq_norm_mul_rpow_le_zeroShortWeight hε hX0 ?_ ?_
          · have := norm_multWindowCoeffOuter_le hη0 (by linarith) hδ0.le (xiZeroCopy_re_pos q)
              (xiZeroCopy_re_lt_one q)
            linarith
          · have := norm_multWindowCoeffOuter_le_div hη0 hη4 hδ0.le hδ (xiZeroCopy_re_pos q)
              (xiZeroCopy_re_lt_one q)
            refine le_trans this ?_
            have hρne := xiZeroCopy_ne_zero q
            have hρ1ne : 1 - (q.1 : ℂ) ≠ 0 := xiZeroCopy_one_sub_ne_zero q
            have hP0 : 0 < ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ :=
              mul_pos (norm_pos_iff.mpr hρne) (norm_pos_iff.mpr hρ1ne)
            gcongr
            norm_num
      _ = 25 * δ ^ 2 * ∑ q ∈ F, zeroShortWeight (X ^ 2) Y (q.1 : ℂ) := by rw [Finset.mul_sum]
      _ ≤ 25 * δ ^ 2 * Z := by gcongr
  -- the two superlevel sets
  have hvolD := volume_ge_norm_zeroSum_le hX0 hr0 F
    (fun q => multWindowCoeff δ η (q.1 : ℂ)) hW
  have hvolE := volume_ge_norm_zeroSum_le hX0 hr0 F
    (fun q => multWindowCoeffOuter δ η (q.1 : ℂ)) hW
  set A := {x : ℝ | x ∈ Set.Icc X (2 * X)
    ∧ r ≤ ‖∑ q ∈ F, multWindowCoeff δ η (q.1 : ℂ) * (x : ℂ) ^ (q.1 : ℂ)‖} with hA
  set B := {x : ℝ | x ∈ Set.Icc X (2 * X)
    ∧ r ≤ ‖∑ q ∈ F, multWindowCoeffOuter δ η (q.1 : ℂ) * (x : ℂ) ^ (q.1 : ℂ)‖} with hB
  have hsub : {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ ε * (δ * x)
      < |Chebyshev.psi (x + δ * x) - Chebyshev.psi x - δ * x|} ⊆ A ∪ B := by
    rintro x ⟨hx, hlt⟩
    have hpt := abs_psi_short_sub_le hε hε1 hX hδ hbig hx
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    have hD : ‖asymInnerSum θ ε X x‖ < r := by
      by_contra h
      exact hcon.1 ⟨hx, le_of_not_gt h⟩
    have hE : ‖asymOuterSum θ ε X x‖ < r := by
      by_contra h
      exact hcon.2 ⟨hx, le_of_not_gt h⟩
    have hXx : δ * X ≤ δ * x := mul_le_mul_of_nonneg_left hx.1 hδ0.le
    have hrx : r ≤ ε / 4 * (δ * x) := by
      rw [hr]
      exact mul_le_mul_of_nonneg_left hXx (by positivity)
    have hx0 : 0 < x := by linarith [hx.1]
    have hδx : 0 < δ * x := mul_pos hδ0 hx0
    linarith
  have hfinA : volume A ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono fun x hx => hx.1) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hfinB : volume B ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono fun x hx => hx.1) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hunion : (volume {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ ε * (δ * x)
      < |Chebyshev.psi (x + δ * x) - Chebyshev.psi x - δ * x|}).toReal
      ≤ (volume A).toReal + (volume B).toReal := by
    rw [← ENNReal.toReal_add hfinA hfinB]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfinA, hfinB⟩)
      (le_trans (measure_mono hsub) (measure_union_le A B))
  refine le_trans hunion ?_
  have hfac : (2 * X) ^ 3 / r ^ 2 * (4 * W * (25 * δ ^ 2 * Z))
      = 12800 / ε ^ 2 * W * X * Z := by
    rw [hr]
    field_simp
    ring
  have hA' : (volume A).toReal ≤ 12800 / ε ^ 2 * W * X * Z := by
    rw [← hfac]
    refine le_trans hvolD ?_
    gcongr
  have hB' : (volume B).toReal ≤ 12800 / ε ^ 2 * W * X * Z := by
    rw [← hfac]
    refine le_trans hvolE ?_
    gcongr
  have e : 25600 / ε ^ 2 * W * X * Z = 12800 / ε ^ 2 * W * X * Z + 12800 / ε ^ 2 * W * X * Z := by
    ring
  rw [e]
  exact add_le_add hA' hB'

/-- **The prime number theorem in almost all short intervals.**  For `1/6 < θ < 1` and
`0 < ε ≤ 1`, the measure of the `x ∈ [X, 2X]` with
`|ψ(x + X^{θ-1}x) - ψ(x) - X^{θ-1}x| > ε X^{θ-1}x` is `o(X)`. -/
theorem tendsto_volume_psi_short_asymptotic {θ ε : ℝ} (hθ : 1 / 6 < θ) (hθ1 : θ < 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Tendsto (fun X : ℝ => (volume {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ ε * (X ^ (θ - 1) * x)
        < |Chebyshev.psi (x + X ^ (θ - 1) * x) - Chebyshev.psi x - X ^ (θ - 1) * x|}).toReal / X)
      atTop (𝓝 0) := by
  have hθ0 : 0 < θ := by linarith
  have hu : 0 < (1 - θ) / 2 := by linarith
  have hu' : (1 - θ) / 2 < 5 / 12 := by linarith
  have hc1 : (1 : ℝ) ≤ 192 / (5 * ε) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hlim := (tendsto_logPow_mul_tsum_zeroShortWeight_seven_twelfths 2 hu hu' hc1).comp
    (tendsto_pow_atTop (two_ne_zero : (2 : ℕ) ≠ 0))
  set K := |xiLineTwoLogDerivConstant| with hK
  have hK0 : 0 ≤ K := abs_nonneg _
  have hlim3 := hlim.const_mul (25600 / ε ^ 2 * (64 * (K + 2)))
  rw [mul_zero] at hlim3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim3 ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    exact div_nonneg ENNReal.toReal_nonneg hX.le
  · have hev1 : ∀ᶠ X : ℝ in atTop, X ^ (θ - 1) ≤ 1 / 2 := by
      have h := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 - θ by linarith)
      have h' := h.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
      refine h'.mono fun X hX => ?_
      rwa [show -(1 - θ) = θ - 1 by ring] at hX
    have hev2 : ∀ᶠ X : ℝ in atTop,
        16 * (64 + 1152 * xiSpectralThreeHalvesMass) / ε ^ 2 ≤ X ^ (2 * θ) :=
      (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 2 * θ)).eventually_ge_atTop _
    filter_upwards [hev1, hev2, eventually_ge_atTop (4 : ℝ)] with X hXδ hXb hX4
    have hX0 : 0 < X := by linarith
    have hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * X ^ (2 * θ) := by
      rw [div_le_iff₀ (by positivity)] at hXb
      linarith
    have hv := volume_psi_short_asymptotic_le hε hε1 hX4 hXδ hbig
    have hW := almostAllHarmonicWeight_le (by linarith : (1 : ℝ) ≤ X)
    rw [← hK] at hW
    set Z := ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2)
      (192 / (5 * ε) * (X ^ 2) ^ (2 * ((1 - θ) / 2))) (q.1 : ℂ) with hZ
    have hZ0 : 0 ≤ Z := tsum_nonneg fun q => zeroShortWeight_nonneg (by positivity)
      (by positivity) _
    show _ / X ≤ 25600 / ε ^ 2 * (64 * (K + 2)) * ((Real.log (X ^ 2) + 2) ^ 2 * Z)
    rw [div_le_iff₀ hX0]
    calc _ ≤ 25600 / ε ^ 2 * almostAllHarmonicWeight X * X * Z := hv
      _ ≤ 25600 / ε ^ 2 * (64 * (K + 2) * (Real.log (X ^ 2) + 2) ^ 2) * X * Z := by gcongr
      _ = 25600 / ε ^ 2 * (64 * (K + 2)) * ((Real.log (X ^ 2) + 2) ^ 2 * Z) * X := by ring

end RHTower

end
