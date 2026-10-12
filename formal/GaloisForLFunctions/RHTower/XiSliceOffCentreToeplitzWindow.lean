import GaloisForLFunctions.RHTower.XiSliceOffCentreTuranWindow
import GaloisForLFunctions.HTGeometry.TrigPolynomialShortArcLowerBound
import GaloisForLFunctions.HTGeometry.RealMatrixQuadraticFormDetPos

/-!
# Off-centre Toeplitz windows: positive Toeplitz minors of every fixed order

Let `g_t(x) = ξ(½+x+it) ξ(½−x+it)` and `a_m = g_t^{(m)}(x₀)/m!`.

**Theorem** (`exists_xiSliceProduct_toeplitzDet_pos_offCentre`).  For every `k ≥ 1` and
`0 < ε ≤ 1/8` there is `t₀` such that for `t ≥ t₀`, `ε ≤ x₀ ≤ ½` and every centre `n ≥ k − 1` with
`(½ − x₀ + ε) log t ≤ n ≤ log t`,

  `det [a_{n+i−j}]_{0 ≤ i, j < k} > 0`.

Every contiguous Toeplitz minor of order `k` whose centre lies in the window is positive; `k = 1` is
the positivity window and `k = 2` the Turán window.

**Mechanism.**  On the saddle circle of the order `n`, `a_{n+i−j} = C R^{j−i} T_{ij}` with
`T_{ij} = ∫₀^π Re(G(θ) e^{−i(i−j)θ}) dθ` (`iteratedDeriv_xiSliceProduct_eq_half_circle_freq`), so
`det[a_{n+i−j}] = C^k det T`.  For real `x`,

  `xᵀ T x = ∫₀^π Re G(θ) |Σ_j x_j e^{ijθ}|² dθ`   (`toeplitz_quadForm_eq`):

the imaginary part of `G` cancels between `(i, j)` and `(j, i)`.  The trigonometric polynomial
has at most a zero of order `k − 1` on the core arc `[δ₀/2, δ₀]`, so
`∫_{δ₀/2}^{δ₀} |p|² ≥ c_k δ₀^{2k−1} ‖x‖²` (`exists_integral_shortArcTrigPoly_sq_ge`), while the arc
beyond the core is exponentially small in `Λ^{1/5}` and polynomially small in `t`.  Hence `xᵀ T x > 0`
for `x ≠ 0` (`integral_weighted_pos_of_arc_bounds_scaled_int`), and a real matrix with positive
quadratic form has positive determinant (`det_pos_of_quadForm_pos`).
-/

open Complex Real Metric intervalIntegral Matrix
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- **Weighted arc positivity with an integral core bound.**  As
`integral_weighted_pos_of_arc_bounds_scaled`, with the pointwise core bound replaced by
`∫_{δ₀/2}^{δ₀} w ≥ W₀ > 0`; the middle and tail losses must be at most `(7/160) W₀` each. -/
theorem integral_weighted_pos_of_arc_bounds_scaled_int {S : ℝ → ℂ} (hSc : Continuous S)
    {w : ℝ → ℝ} (hwc : Continuous w)
    {R ℓ F₁ D K δ₀ δ E U W₀ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ) (hK : 1 ≤ K) (hU : 1 ≤ U)
    (hF₁lo : 9 / 10 * ℓ ≤ F₁) (hF₁hi : F₁ ≤ 2 * ℓ) (hD : D ≤ K * ℓ) (hD0 : 0 ≤ D)
    (hb : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / (1000 * K) →
      ‖S θ‖ ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
      ∧ (|F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * D) * θ ^ 3 ≤ Real.pi / 2 →
        Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3)
          * Real.cos (|F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * D) * θ ^ 3) ≤ (S θ).re))
    (htail : ∀ θ : ℝ, 1 / (1000 * K) ≤ θ → θ ≤ U → ‖S θ‖ ≤ E)
    (hw0 : ∀ θ, 0 ≤ θ → θ ≤ U → 0 ≤ w θ) (hw2 : ∀ θ, 0 ≤ θ → θ ≤ U → w θ ≤ 2)
    (hW : W₀ ≤ ∫ θ in (δ₀ / 2)..δ₀, w θ) (hW₀ : 0 < W₀)
    (hδ₀ : 0 < δ₀) (hδ₀δ : δ₀ ≤ δ) (hδ : δ ≤ 1 / (1000 * K))
    (hcore : R * ℓ * δ₀ ^ 2 ≤ 1) (hphase : (1 + 128 * K) * (R * ℓ) * δ ^ 3 ≤ 3 / 2)
    (hmid : 2 * (1 / 1000 * Real.exp (-(R * ℓ) * δ ^ 2 / 8)) ≤ 7 / 160 * W₀)
    (hE : 2 * (U * E) ≤ 7 / 160 * W₀) :
    0 < ∫ θ in (0 : ℝ)..U, (S θ).re * w θ := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = R * ℓ := ⟨_, rfl⟩
  rw [← hΛ] at hcore hphase hmid
  have hF₁0 : 0 ≤ F₁ := by linarith
  have hK0 : 0 < K := by linarith
  obtain ⟨θK, hθK⟩ : ∃ θK : ℝ, θK = 1 / (1000 * K) := ⟨_, rfl⟩
  rw [← hθK] at hb htail hδ
  have hθK0 : 0 < θK := by rw [hθK]; positivity
  have hθK1 : θK ≤ 1 / 1000 := by
    rw [hθK]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hKθK : K * θK = 1 / 1000 := by rw [hθK]; field_simp
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun θ : ℝ => (S θ).re * w θ) MeasureTheory.volume a b :=
    fun a b => ((Complex.continuous_re.comp hSc).mul hwc).intervalIntegrable a b
  have hpi : θK ≤ U := by linarith
  have hδU : δ ≤ U := by linarith
  have hδ₀U : δ₀ ≤ U := by linarith
  have hcoreθ : ∀ θ ∈ Set.Icc 0 δ,
      7 / 8 * Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2) ≤ (S θ).re := by
    intro θ hθ
    have hθ4 : θ ≤ θK := hθ.2.trans hδ
    have hθ3 : θ ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ hθ.1 hθ.2 3
    have hθ3' : 0 ≤ θ ^ 3 := pow_nonneg hθ.1 3
    have h1 : |F₁| * R * θ ^ 3 / 6 ≤ Λ / 3 * θ ^ 3 := by
      rw [abs_of_nonneg hF₁0, hΛ]
      have := mul_le_mul_of_nonneg_right hF₁hi (mul_nonneg hR.le hθ3')
      linarith
    have h2 : 128 / 3 * (R * D) * θ ^ 3 ≤ 128 / 3 * (K * Λ) * θ ^ 3 := by
      rw [hΛ]
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hR.le) hθ3'
      linarith
    have h3 : (1 + 128 * K) * Λ * θ ^ 3 ≤ (1 + 128 * K) * Λ * δ ^ 3 :=
      mul_le_mul_of_nonneg_left hθ3 (by rw [hΛ]; positivity)
    have hc3 : 0 ≤ 128 / 3 * (R * D) * θ ^ 3 := by positivity
    have ha : 0 ≤ |F₁| * R * θ ^ 3 / 6 := by positivity
    set φ := |F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * D) * θ ^ 3 with hφdef
    have hφ : φ ≤ 1 / 2 := by rw [hφdef]; linarith
    have hφ0 : 0 ≤ φ := by rw [hφdef]; linarith
    have hlow := (hb θ hθ.1 hθ4).2 (by linarith [Real.pi_gt_three])
    have hcos : 7 / 8 ≤ Real.cos φ := by
      have h1 := Real.one_sub_sq_div_two_le_cos (x := φ)
      have h2 : φ ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ hφ0 hφ 2
      linarith
    have hexp : Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2)
        ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3) := by
      apply Real.exp_le_exp.mpr
      have := hφ; rw [hφdef] at this; linarith
    calc 7 / 8 * Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2)
        ≤ Real.cos φ * Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3) :=
          mul_le_mul hcos hexp (Real.exp_pos _).le (by linarith)
      _ = Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3) * Real.cos φ := by
          ring
      _ ≤ _ := hlow
  -- `Re S ≥ 7/40` on `[0, δ₀]`
  have hcore740 : ∀ θ, 0 ≤ θ → θ ≤ δ₀ → (7 / 40 : ℝ) ≤ (S θ).re := by
    intro θ h0 h1
    have hc := hcoreθ θ ⟨h0, h1.trans hδ₀δ⟩
    have hθ2 : θ ^ 2 ≤ δ₀ ^ 2 := pow_le_pow_left₀ h0 h1 2
    have hq : F₁ * R * (1 - Real.cos θ) ≤ 1 := by
      have h1 := one_sub_cos_le_half_sq θ
      have h0' : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
      calc F₁ * R * (1 - Real.cos θ) ≤ (2 * ℓ) * R * (θ ^ 2 / 2) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hF₁hi hR.le) h1 h0' (by positivity)
        _ = Λ * θ ^ 2 := by rw [hΛ]; ring
        _ ≤ Λ * δ₀ ^ 2 := by gcongr; rw [hΛ]; positivity
        _ ≤ 1 := hcore
    have he : 1 / 5 ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2) := by
      have h5 := exp_three_halves_le_five
      have : Real.exp (-(3 / 2)) ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      rw [Real.exp_neg] at this
      have hpos := Real.exp_pos (3 / 2)
      calc (1 / 5 : ℝ) ≤ (Real.exp (3 / 2))⁻¹ := by
            rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hpos h5
        _ ≤ _ := this
    linarith
  -- `|S| ≤ e^{−Λδ²/8}` on `[δ, θK]`
  have hmidθ : ∀ θ, δ ≤ θ → θ ≤ θK → ‖S θ‖ ≤ Real.exp (-Λ * δ ^ 2 / 8) := by
    intro θ hθ1 hθ2
    have hθ0 : 0 ≤ θ := hδ₀.le.trans (hδ₀δ.trans hθ1)
    have hn := (hb θ hθ0 hθ2).1
    have hcos := one_sub_cos_ge_sq_div_five (θ := θ)
      (by rw [abs_of_nonneg hθ0]; linarith [Real.pi_gt_three, hθ2])
    have h1 : 9 / 10 * ℓ * R * (θ ^ 2 / 5) ≤ F₁ * R * (1 - Real.cos θ) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hF₁lo hR.le) hcos (by positivity)
        (mul_nonneg hF₁0 hR.le)
    have h2 : 128 / 3 * (R * D) * θ ^ 3 ≤ 128 / 3 * (R * ℓ) * θ ^ 2 * (1 / 1000) := by
      have hKθ : K * θ ≤ 1 / 1000 := by
        rw [← hKθK]; exact mul_le_mul_of_nonneg_left hθ2 hK0.le
      have hDR : R * D ≤ R * (K * ℓ) := mul_le_mul_of_nonneg_left hD hR.le
      calc 128 / 3 * (R * D) * θ ^ 3 ≤ 128 / 3 * (R * (K * ℓ)) * θ ^ 3 := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg hθ0 3); linarith
        _ = 128 / 3 * (R * ℓ) * θ ^ 2 * (K * θ) := by ring
        _ ≤ 128 / 3 * (R * ℓ) * θ ^ 2 * (1 / 1000) :=
            mul_le_mul_of_nonneg_left hKθ (by positivity)
    have hδθ : δ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ (hδ₀.le.trans hδ₀δ) hθ1 2
    have hexp : Real.exp (-(F₁ * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
        ≤ Real.exp (-Λ * δ ^ 2 / 8) := by
      apply Real.exp_le_exp.mpr; rw [hΛ]
      have hΛθ : 0 ≤ R * ℓ * θ ^ 2 := by positivity
      have h4 : R * ℓ * δ ^ 2 ≤ R * ℓ * θ ^ 2 :=
        mul_le_mul_of_nonneg_left hδθ (by positivity)
      linarith only [h1, h2, h4, hΛθ]
    exact hn.trans hexp
  -- the five pieces
  have hI0 : 0 ≤ ∫ θ in (0 : ℝ)..(δ₀ / 2), (S θ).re * w θ :=
    intervalIntegral.integral_nonneg (by linarith) fun θ hθ =>
      mul_nonneg ((by norm_num : (0 : ℝ) ≤ 7 / 40).trans (hcore740 θ hθ.1 (by linarith [hθ.2])))
        (hw0 θ hθ.1 (by linarith [hθ.2]))
  have hI1 : 7 / 40 * W₀ ≤ ∫ θ in (δ₀ / 2)..δ₀, (S θ).re * w θ := by
    have hwi : IntervalIntegrable (fun θ => 7 / 40 * w θ) MeasureTheory.volume (δ₀ / 2) δ₀ :=
      (continuous_const.mul hwc).intervalIntegrable _ _
    have := intervalIntegral.integral_mono_on (by linarith : δ₀ / 2 ≤ δ₀) hwi (hi (δ₀ / 2) δ₀)
      (fun θ hθ => (show 7 / 40 * w θ ≤ (S θ).re * w θ from
        mul_le_mul_of_nonneg_right (hcore740 θ (by linarith [hθ.1]) hθ.2)
          (hw0 θ (by linarith [hθ.1]) (hθ.2.trans hδ₀U))))
    rw [intervalIntegral.integral_const_mul] at this
    nlinarith
  have hI2 : 0 ≤ ∫ θ in δ₀..δ, (S θ).re * w θ :=
    intervalIntegral.integral_nonneg hδ₀δ fun θ hθ =>
      mul_nonneg (le_trans (by positivity) (hcoreθ θ ⟨hδ₀.le.trans hθ.1, hθ.2⟩))
        (hw0 θ (hδ₀.le.trans hθ.1) (hθ.2.trans hδU))
  have hI3 : -(2 * (1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8))) ≤ ∫ θ in δ..θK, (S θ).re * w θ := by
    have := intervalIntegral.integral_mono_on hδ
      (continuous_const.intervalIntegrable δ θK) (hi δ θK)
      (fun θ hθ => (show -(2 * Real.exp (-Λ * δ ^ 2 / 8)) ≤ (S θ).re * w θ from by
        have hθ0 : 0 ≤ θ := hδ₀.le.trans (hδ₀δ.trans hθ.1)
        have hn := hmidθ θ hθ.1 hθ.2
        have hab := Complex.abs_re_le_norm (S θ)
        have hw0' := hw0 θ hθ0 (hθ.2.trans hpi)
        have hw2' := hw2 θ hθ0 (hθ.2.trans hpi)
        have hprod : |(S θ).re * w θ| ≤ 2 * Real.exp (-Λ * δ ^ 2 / 8) := by
          rw [abs_mul, abs_of_nonneg hw0']
          calc |(S θ).re| * w θ ≤ Real.exp (-Λ * δ ^ 2 / 8) * 2 :=
                mul_le_mul (hab.trans hn) hw2' hw0' (Real.exp_pos _).le
            _ = 2 * Real.exp (-Λ * δ ^ 2 / 8) := by ring
        linarith [neg_abs_le ((S θ).re * w θ)]))
    have hδ0 : 0 ≤ δ := hδ₀.le.trans hδ₀δ
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have hlen : θK - δ ≤ 1 / 1000 := by linarith
    have hE0 : 0 ≤ 2 * Real.exp (-Λ * δ ^ 2 / 8) := by positivity
    have := mul_le_mul_of_nonneg_right hlen hE0
    nlinarith
  have hI4 : -(2 * (U * E)) ≤ ∫ θ in θK..U, (S θ).re * w θ := by
    have hE0 : 0 ≤ E := le_trans (norm_nonneg _) (htail θK le_rfl hpi)
    have := intervalIntegral.integral_mono_on hpi
      (continuous_const.intervalIntegrable θK U) (hi θK U)
      (fun θ hθ => (show -(2 * E) ≤ (S θ).re * w θ from by
        have hθ0 : 0 ≤ θ := hθK0.le.trans hθ.1
        have hn := htail θ hθ.1 hθ.2
        have hab := Complex.abs_re_le_norm (S θ)
        have hw0' := hw0 θ hθ0 hθ.2
        have hw2' := hw2 θ hθ0 hθ.2
        have hprod : |(S θ).re * w θ| ≤ 2 * E := by
          rw [abs_mul, abs_of_nonneg hw0']
          calc |(S θ).re| * w θ ≤ E * 2 := mul_le_mul (hab.trans hn) hw2' hw0' hE0
            _ = 2 * E := by ring
        linarith [neg_abs_le ((S θ).re * w θ)]))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have h1 : (U - θK) * (2 * E) ≤ U * (2 * E) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  have hsplit : ∫ θ in (0 : ℝ)..U, (S θ).re * w θ
      = (∫ θ in (0 : ℝ)..(δ₀ / 2), (S θ).re * w θ) + (∫ θ in (δ₀ / 2)..δ₀, (S θ).re * w θ)
        + (∫ θ in δ₀..δ, (S θ).re * w θ) + (∫ θ in δ..θK, (S θ).re * w θ)
        + ∫ θ in θK..U, (S θ).re * w θ := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi 0 (δ₀ / 2)) (hi (δ₀ / 2) δ₀),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 δ₀) (hi δ₀ δ),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 δ) (hi δ θK),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 θK) (hi θK U)]
  rw [hsplit]
  have hmid' : 2 * (1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8)) ≤ 7 / 160 * W₀ := hmid
  have hpos : 0 < 7 / 40 * W₀ := by positivity
  linarith only [hI0, hI1, hI2, hI3, hI4, hmid', hE, hpos]

open GaloisForLFunctions.HTGeometry in
/-- The pointwise Toeplitz form: `Σ_{i,j} x_i x_j Re(G e^{−i(i−j)θ}) = Re G · |Σ_j x_j e^{ijθ}|²`. -/
theorem toeplitz_pointwise_eq {k : ℕ} (g : ℂ) (θ : ℝ) (x : Fin k → ℝ) :
    ∑ i : Fin k, ∑ j : Fin k, x i * x j
        * (g * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * θ : ℝ) : ℂ) * I)).re
      = g.re * ‖shortArcTrigPoly (fun j => (x j : ℂ)) θ‖ ^ 2 := by
  set p : ℂ := shortArcTrigPoly (fun j => (x j : ℂ)) θ with hp
  have hconj : (starRingEnd ℂ) p
      = ∑ i : Fin k, (x i : ℂ) * Complex.exp (-(((i : ℕ) : ℂ) * (θ : ℂ) * I)) := by
    rw [hp, shortArcTrigPoly, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_I,
      Complex.conj_ofReal, Complex.conj_natCast]
    congr 1
    ring_nf
  have hprod : (starRingEnd ℂ) p * p
      = ∑ i : Fin k, ∑ j : Fin k, ((x i * x j : ℝ) : ℂ)
          * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * θ : ℝ) : ℂ) * I) := by
    rw [hconj, hp, shortArcTrigPoly, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have he : Complex.exp (-((((i : ℕ) : ℂ) - ((j : ℕ) : ℂ)) * (θ : ℂ)) * I)
        = Complex.exp (-(((i : ℕ) : ℂ) * (θ : ℂ) * I))
          * Complex.exp (((j : ℕ) : ℂ) * (θ : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    push_cast
    rw [he]
    ring
  have hnorm : (starRingEnd ℂ) p * p = ((‖p‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hre : (g * ((starRingEnd ℂ) p * p)).re = g.re * ‖p‖ ^ 2 := by
    rw [hnorm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [← hre, hprod, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show g * (((x i * x j : ℝ) : ℂ) * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * θ : ℝ) : ℂ) * I))
      = ((x i * x j : ℝ) : ℂ) * (g * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * θ : ℝ) : ℂ) * I))
      by ring, Complex.re_ofReal_mul]

open GaloisForLFunctions.HTGeometry in
/-- **The Toeplitz form of the arc.**  For real `x`,
`Σ_{i,j} x_i x_j ∫₀^π Re(G e^{−i(i−j)θ}) = ∫₀^π Re G |Σ_j x_j e^{ijθ}|²`. -/
theorem toeplitz_quadForm_eq {k : ℕ} {G : ℝ → ℂ} (hG : Continuous G) (x : Fin k → ℝ) :
    ∑ i : Fin k, ∑ j : Fin k, x i * x j * ∫ θ in (0 : ℝ)..Real.pi,
        (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * θ : ℝ) : ℂ) * I)).re
      = ∫ θ in (0 : ℝ)..Real.pi, (G θ).re * ‖shortArcTrigPoly (fun j => (x j : ℂ)) θ‖ ^ 2 := by
  have hint : ∀ i j : Fin k, IntervalIntegrable (fun θ => x i * x j
      * (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * θ : ℝ) : ℂ) * I)).re)
      MeasureTheory.volume 0 Real.pi := by
    intro i j
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  have h1 : ∀ i j : Fin k, x i * x j * ∫ θ in (0 : ℝ)..Real.pi,
      (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * θ : ℝ) : ℂ) * I)).re
      = ∫ θ in (0 : ℝ)..Real.pi, x i * x j
        * (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * θ : ℝ) : ℂ) * I)).re :=
    fun i j => (intervalIntegral.integral_const_mul _ _).symm
  simp_rw [h1]
  have h2 : ∀ i : Fin k, ∑ j : Fin k, ∫ θ in (0 : ℝ)..Real.pi, x i * x j
      * (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * θ : ℝ) : ℂ) * I)).re
      = ∫ θ in (0 : ℝ)..Real.pi, ∑ j : Fin k, x i * x j
        * (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * θ : ℝ) : ℂ) * I)).re :=
    fun i => (intervalIntegral.integral_finsetSum fun j _ => hint i j).symm
  simp_rw [h2]
  have h3 : (∫ θ in (0 : ℝ)..Real.pi, ∑ i : Fin k, ∑ j : Fin k, x i * x j
      * (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * θ : ℝ) : ℂ) * I)).re)
      = ∑ i : Fin k, ∫ θ in (0 : ℝ)..Real.pi, ∑ j : Fin k, x i * x j
        * (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * θ : ℝ) : ℂ) * I)).re :=
    intervalIntegral.integral_finsetSum fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _
  rw [← h3]
  congr 1
  funext θ
  exact toeplitz_pointwise_eq (G θ) θ x

open GaloisForLFunctions.HTGeometry in
/-- **The Toeplitz form on an arbitrary arc and angle map.**  For real `x` and continuous `G`, `φ`,
`Σ_{i,j} x_i x_j ∫_a^b Re(G e^{−i(i−j)φ}) = ∫_a^b Re G |Σ_j x_j e^{ijφ}|²`. -/
theorem toeplitz_quadForm_eq_gen {k : ℕ} {G : ℝ → ℂ} (hG : Continuous G) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (a b : ℝ) (x : Fin k → ℝ) :
    ∑ i : Fin k, ∑ j : Fin k, x i * x j * ∫ θ in a..b,
        (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * φ θ : ℝ) : ℂ) * I)).re
      = ∫ θ in a..b, (G θ).re * ‖shortArcTrigPoly (fun j => (x j : ℂ)) (φ θ)‖ ^ 2 := by
  have hint : ∀ i j : Fin k, IntervalIntegrable (fun θ => x i * x j
      * (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * φ θ : ℝ) : ℂ) * I)).re)
      MeasureTheory.volume a b := by
    intro i j
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  have h1 : ∀ i j : Fin k, x i * x j * ∫ θ in a..b,
      (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * φ θ : ℝ) : ℂ) * I)).re
      = ∫ θ in a..b, x i * x j
        * (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * φ θ : ℝ) : ℂ) * I)).re :=
    fun i j => (intervalIntegral.integral_const_mul _ _).symm
  simp_rw [h1]
  have h2 : ∀ i : Fin k, ∑ j : Fin k, ∫ θ in a..b, x i * x j
      * (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * φ θ : ℝ) : ℂ) * I)).re
      = ∫ θ in a..b, ∑ j : Fin k, x i * x j
        * (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * φ θ : ℝ) : ℂ) * I)).re :=
    fun i => (intervalIntegral.integral_finsetSum fun j _ => hint i j).symm
  simp_rw [h2]
  have h3 : (∫ θ in a..b, ∑ i : Fin k, ∑ j : Fin k, x i * x j
      * (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * φ θ : ℝ) : ℂ) * I)).re)
      = ∑ i : Fin k, ∫ θ in a..b, ∑ j : Fin k, x i * x j
        * (G θ * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * φ θ : ℝ) : ℂ) * I)).re :=
    intervalIntegral.integral_finsetSum fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _
  rw [← h3]
  congr 1
  funext θ
  exact toeplitz_pointwise_eq (G θ) (φ θ) x

/-- Conjugation by the diagonal `R^{−i}` does not change the determinant. -/
theorem det_eq_pow_mul_det_of_diag_conj {k : ℕ} {C R : ℝ} (hR : 0 < R)
    (T M : Matrix (Fin k) (Fin k) ℝ) (hM : ∀ i j, M i j = C * R ^ (j : ℕ) / R ^ (i : ℕ) * T i j) :
    M.det = C ^ k * T.det := by
  have hMe : M = Matrix.diagonal (fun i : Fin k => (R ^ (i : ℕ))⁻¹) * (C • T)
      * Matrix.diagonal (fun j : Fin k => R ^ (j : ℕ)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul, hM]
    have : R ^ (i : ℕ) ≠ 0 := pow_ne_zero _ hR.ne'
    field_simp
  rw [hMe, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    Matrix.det_smul, Fintype.card_fin]
  have hprod : (∏ i : Fin k, (R ^ (i : ℕ))⁻¹) * ∏ j : Fin k, R ^ (j : ℕ) = 1 := by
    rw [Finset.prod_inv_distrib, inv_mul_cancel₀]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hR.ne'
  calc (∏ i : Fin k, (R ^ (i : ℕ))⁻¹) * (C ^ k * T.det) * ∏ j : Fin k, R ^ (j : ℕ)
      = ((∏ i : Fin k, (R ^ (i : ℕ))⁻¹) * ∏ j : Fin k, R ^ (j : ℕ)) * (C ^ k * T.det) := by ring
    _ = C ^ k * T.det := by rw [hprod, one_mul]

open GaloisForLFunctions.HTGeometry in
/-- The shift `θ ↦ θ + a` of a trigonometric polynomial rotates its coefficients. -/
theorem shortArcTrigPoly_add {k : ℕ} (y : Fin k → ℂ) (a θ : ℝ) :
    shortArcTrigPoly y (θ + a)
      = shortArcTrigPoly (fun j => y j * Complex.exp (((j : ℕ) : ℂ) * (a : ℂ) * I)) θ := by
  unfold shortArcTrigPoly
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc (y j), ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The scale factor of the entry `a_{n+i−j}`: `X/(πR^{n+i−j}) = C R^j/R^i` with
`C = X/(πRⁿ)`. -/
theorem scale_entry_eq {X R : ℝ} {n i j : ℕ} (hR : 0 < R) (hji : j ≤ n + i) (V : ℝ) :
    X / (Real.pi * R ^ (n + i - j)) * V = X / (Real.pi * R ^ n) * R ^ j / R ^ i * V := by
  have hpow : R ^ (n + i - j) * R ^ j = R ^ n * R ^ i := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hRn : R ^ (n + i - j) ≠ 0 := pow_ne_zero _ hR.ne'
  have hRi : R ^ i ≠ 0 := pow_ne_zero _ hR.ne'
  have hRn' : R ^ n ≠ 0 := pow_ne_zero _ hR.ne'
  have hRj : R ^ j ≠ 0 := pow_ne_zero _ hR.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have e : R ^ (n + i - j) = R ^ n * R ^ i / R ^ j := by
    rw [eq_div_iff hRj, hpow]
  rw [e]
  field_simp

/-- **Positive Toeplitz determinant from saddle data.**  Under the saddle conditions of
`xiSliceProduct_turan_of_saddle_shift` at a centre `n ≥ k − 1`, given the short-arc constants
`(c, h₀)` of order `k` and the losses
`2·10⁻³ e^{−Λ^{1/5}/8}, 2πE ≤ (7/160) c (Λ^{−1/2}/2)^{2k−1}/k²`, the Toeplitz matrix
`[a_{n+i−j}]_{i,j<k}` has positive determinant. -/
theorem xiSliceProduct_toeplitzDet_pos_of_saddle_shift {η R₁ K t u x₀ R E c h₀ : ℝ} {n k : ℕ}
    (hk : 1 ≤ k) (hnk : k - 1 ≤ n)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hR₁ : 1 ≤ R₁) (hKdef : K = R₁ / (2 * η)) (ht8 : 8 ≤ t)
    (hu0 : 0 < u) (hx₀ : 0 ≤ x₀) (hR0 : 0 < R) (hRa : 1 / 2 + 2 * η ≤ x₀ + R)
    (hRb : x₀ + R ≤ R₁) (hRt : x₀ + R ≤ t / 2)
    (hsad : (HTGeometry.scaledLogDeriv (xiSliceShift t x₀) R).re = n)
    (hF₁lo : 9 / 10 * u ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re)
    (hF₁hi : (deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re ≤ 2 * u)
    (hKd : xiSliceDiscConstantEuler η t R ≤ 2 * η * u)
    (htail : ∀ θ : ℝ, 1 / (1000 * K) ≤ θ → θ ≤ Real.pi →
      ‖HTGeometry.saddleArc (xiSliceShift t x₀) R n θ‖ ≤ E)
    (hΛ1 : 1 ≤ R * u)
    (hE3 : (R * u) ^ (-(2 / 5) : ℝ) < 1 / (1000 * K))
    (hE4 : (R * u) ^ (-(1 / 5) : ℝ) < 3 / (2 * (1 + 128 * K)))
    (hc : 0 < c)
    (hshort : ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ y : Fin k → ℂ,
      c * h ^ (2 * k - 1) * ‖y‖ ^ 2
        ≤ ∫ θ in (0 : ℝ)..h, ‖GaloisForLFunctions.HTGeometry.shortArcTrigPoly y θ‖ ^ 2)
    (hΛh : (R * u) ^ (-(1 / 2) : ℝ) / 2 ≤ h₀)
    (hmidΛ : 2 * (1 / 1000 * Real.exp (-((R * u) ^ (1 / 5 : ℝ)) / 8))
      ≤ 7 / 160 * (c * ((R * u) ^ (-(1 / 2) : ℝ) / 2) ^ (2 * k - 1) / (k : ℝ) ^ 2))
    (htailΛ : 2 * (Real.pi * E)
      ≤ 7 / 160 * (c * ((R * u) ^ (-(1 / 2) : ℝ) / 2) ^ (2 * k - 1) / (k : ℝ) ^ 2)) :
    0 < (Matrix.of fun i j : Fin k => (((n + i - j : ℕ).factorial : ℂ)⁻¹
      * iteratedDeriv (n + i - j) (xiSliceProduct t) (x₀ : ℂ)).re).det := by
  have hR₁0 : 0 < R₁ := by linarith
  have hRR₁ : R ≤ R₁ := by linarith
  have hK1 : 1 ≤ K := by rw [hKdef, le_div_iff₀ (by positivity)]; linarith
  have hKd0 : 0 ≤ xiSliceDiscConstantEuler η t R := by
    unfold xiSliceDiscConstantEuler
    have h1 : 0 ≤ Real.log (3 * t / 2) := Real.log_nonneg (by linarith)
    have h2 := xiEulerConstant_pos hη
    have h3 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    exact add_nonneg (mul_nonneg hη.le (by linarith [Real.pi_pos]))
      (mul_nonneg hR0.le (by linarith [Real.pi_pos]))
  obtain ⟨D, hDdef⟩ : ∃ D, D = xiSliceDiscConstantEuler η t R * R / (4 * η ^ 2) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hDdef]; exact div_nonneg (mul_nonneg hKd0 hR0.le) (by positivity)
  have hD : D ≤ K * u := by
    rw [hDdef, div_le_iff₀ (by positivity), hKdef]
    have e : R₁ / (2 * η) * u * (4 * η ^ 2) = 2 * η * u * R₁ := by field_simp; ring
    rw [e]
    calc xiSliceDiscConstantEuler η t R * R ≤ xiSliceDiscConstantEuler η t R * R₁ :=
          mul_le_mul_of_nonneg_left hRR₁ hKd0
      _ ≤ 2 * η * u * R₁ := mul_le_mul_of_nonneg_right hKd hR₁0.le
  have hcub : ∀ θ : ℝ, 32 * xiSliceDiscConstantEuler η t R / η ^ 2 * R ^ 2 * θ ^ 3 / 3
      = 128 / 3 * (R * D) * θ ^ 3 := by
    intro θ; rw [hDdef]; field_simp; ring
  have hR₁θ : R₁ * (1 / (1000 * K)) = η / 500 := by rw [hKdef]; field_simp; ring
  have hb : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / (1000 * K) →
      ‖HTGeometry.saddleArc (xiSliceShift t x₀) R n θ‖
        ≤ Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re
          * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
      ∧ (|(deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re| * R * θ ^ 3 / 6
          + 128 / 3 * (R * D) * θ ^ 3 ≤ Real.pi / 2 →
        Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re * R
            * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3)
          * Real.cos (|(deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re| * R * θ ^ 3 / 6
            + 128 / 3 * (R * D) * θ ^ 3)
          ≤ (HTGeometry.saddleArc (xiSliceShift t x₀) R n θ).re) := by
    intro θ hθ0 hθ
    have hRθ : R * θ ≤ η / 2 := by
      have h1 : R * θ ≤ R₁ * θ := mul_le_mul_of_nonneg_right hRR₁ hθ0
      have h2 : R₁ * θ ≤ R₁ * (1 / (1000 * K)) := mul_le_mul_of_nonneg_left hθ hR₁0.le
      linarith
    have h := xiSliceShift_saddleArc_bounds hη (by linarith) ht8 hR0 hRa hRt hθ0 hRθ
    rw [hsad, hcub θ] at h
    exact h
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = R * u := ⟨_, rfl⟩
  rw [← hΛ] at hΛ1 hE3 hE4 hΛh hmidΛ htailΛ
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀, δ₀ = Λ ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = Λ ^ (-(2 / 5) : ℝ) := ⟨_, rfl⟩
  rw [← hδ₀] at hΛh hmidΛ htailΛ
  have hδ₀pos : 0 < δ₀ := hδ₀ ▸ Real.rpow_pos_of_pos hΛ0 _
  have hδ₀δ : δ₀ ≤ δ := by
    rw [hδ₀, hδ]; exact Real.rpow_le_rpow_of_exponent_le hΛ1 (by norm_num)
  have hδθ : δ ≤ 1 / (1000 * K) := by rw [hδ]; exact hE3.le
  have hcore : Λ * δ₀ ^ 2 ≤ 1 := by rw [hδ₀]; exact (mul_rpow_neg_half_sq hΛ0).le
  have hphase : (1 + 128 * K) * Λ * δ ^ 3 ≤ 3 / 2 := by
    have := mul_rpow_neg_two_fifths_cube hΛ0
    rw [hδ, mul_assoc, this]
    have h4 := hE4.le
    rw [le_div_iff₀ (by positivity)] at h4
    linarith
  have hmidexp : Real.exp (-Λ * δ ^ 2 / 8) = Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8) := by
    congr 1
    rw [hδ, ← mul_rpow_neg_two_fifths_sq hΛ0]; ring
  have hSc : Continuous fun θ : ℝ => HTGeometry.saddleArc (xiSliceShift t x₀) R n θ := by
    have hg := differentiable_xiSliceShift t x₀
    have : Continuous fun θ : ℝ => xiSliceShift t x₀ ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
      hg.continuous.comp (by fun_prop)
    simp only [HTGeometry.saddleArc]
    fun_prop
  subst hΛ
  have hU : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  -- the Toeplitz matrix of the arc
  set T : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => ∫ θ in (0 : ℝ)..Real.pi,
    (HTGeometry.saddleArc (xiSliceShift t x₀) R n θ
      * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * θ : ℝ) : ℂ) * I)).re with hT
  have hTpos : ∀ x : Fin k → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (T *ᵥ x) := by
    intro x hx
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set p : ℝ → ℂ := fun θ =>
      GaloisForLFunctions.HTGeometry.shortArcTrigPoly (fun j => (x j : ℂ)) θ with hp
    have hpc : Continuous p := GaloisForLFunctions.HTGeometry.continuous_shortArcTrigPoly _
    set Kx : ℝ := ((k : ℝ) * ‖x‖) ^ 2 with hKx
    have hKx0 : 0 < Kx := by rw [hKx]; positivity
    have hpbd : ∀ θ, ‖p θ‖ ^ 2 ≤ Kx := by
      intro θ
      have h1 : ‖p θ‖ ≤ (k : ℝ) * ‖x‖ := by
        simp only [hp, GaloisForLFunctions.HTGeometry.shortArcTrigPoly]
        calc ‖∑ j : Fin k, (x j : ℂ) * Complex.exp (((j : ℕ) : ℂ) * (θ : ℂ) * I)‖
            ≤ ∑ j : Fin k, ‖(x j : ℂ) * Complex.exp (((j : ℕ) : ℂ) * (θ : ℂ) * I)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _j : Fin k, ‖x‖ := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [norm_mul, show ((j : ℕ) : ℂ) * (θ : ℂ) * I = ((((j : ℕ) : ℝ) * θ : ℝ) : ℂ) * I
                by push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
              exact norm_le_pi_norm x j
          _ = (k : ℝ) * ‖x‖ := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hKx]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    -- the core mass of `|p|²`
    have hcoreW : c * (δ₀ / 2) ^ (2 * k - 1) / (k : ℝ) ^ 2
        ≤ ∫ θ in (δ₀ / 2)..δ₀, ‖p θ‖ ^ 2 / Kx := by
      have hshift := intervalIntegral.integral_comp_add_right (fun θ => ‖p θ‖ ^ 2 / Kx) (δ₀ / 2)
        (a := 0) (b := δ₀ / 2)
      rw [zero_add, show δ₀ / 2 + δ₀ / 2 = δ₀ by ring] at hshift
      rw [← hshift]
      set y : Fin k → ℂ := fun j => (x j : ℂ) * Complex.exp (((j : ℕ) : ℂ) * ((δ₀ / 2 : ℝ) : ℂ) * I)
        with hy
      have hpy : ∀ θ, p (θ + δ₀ / 2) = GaloisForLFunctions.HTGeometry.shortArcTrigPoly y θ := by
        intro θ
        simp only [hp, hy]
        exact shortArcTrigPoly_add _ _ _
      have hyn : ‖y‖ = ‖x‖ := by
        have hj : ∀ j, ‖y j‖ = ‖x j‖ := by
          intro j
          simp only [hy]
          rw [norm_mul, show ((j : ℕ) : ℂ) * ((δ₀ / 2 : ℝ) : ℂ) * I
            = ((((j : ℕ) : ℝ) * (δ₀ / 2) : ℝ) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
        refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_)
          ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_)
        · rw [hj]; exact norm_le_pi_norm x j
        · rw [← hj]; exact norm_le_pi_norm y j
      have hs := hshort (δ₀ / 2) (by positivity) hΛh y
      rw [hyn] at hs
      simp_rw [hpy]
      rw [intervalIntegral.integral_div]
      rw [le_div_iff₀ hKx0, hKx]
      calc c * (δ₀ / 2) ^ (2 * k - 1) / (k : ℝ) ^ 2 * ((k : ℝ) * ‖x‖) ^ 2
          = c * (δ₀ / 2) ^ (2 * k - 1) * ‖x‖ ^ 2 := by field_simp
        _ ≤ _ := hs
    have hwpos := integral_weighted_pos_of_arc_bounds_scaled_int (w := fun θ => ‖p θ‖ ^ 2 / Kx)
      hSc (by fun_prop) hR0 hu0 hK1 hU hF₁lo hF₁hi hD hD0 hb htail
      (fun θ _ _ => by positivity)
      (fun θ _ _ => by
        have := hpbd θ
        rw [div_le_iff₀ hKx0]; nlinarith)
      hcoreW (by positivity) hδ₀pos hδ₀δ hδθ hcore hphase
      (by rw [hmidexp]; exact hmidΛ) (by linarith only [htailΛ])
    have hform := toeplitz_quadForm_eq hSc x
    have hlhs : x ⬝ᵥ (T *ᵥ x) = ∑ i : Fin k, ∑ j : Fin k, x i * x j * ∫ θ in (0 : ℝ)..Real.pi,
        (HTGeometry.saddleArc (xiSliceShift t x₀) R n θ
          * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * θ : ℝ) : ℂ) * I)).re := by
      simp only [dotProduct, Matrix.mulVec, hT, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hlhs, hform]
    have hmul : ∫ θ in (0 : ℝ)..Real.pi,
        (HTGeometry.saddleArc (xiSliceShift t x₀) R n θ).re * ‖p θ‖ ^ 2
        = Kx * ∫ θ in (0 : ℝ)..Real.pi,
          (HTGeometry.saddleArc (xiSliceShift t x₀) R n θ).re * (‖p θ‖ ^ 2 / Kx) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext θ
      field_simp
    simp only [hp] at hmul
    rw [hmul]
    exact mul_pos hKx0 hwpos
  have hTdet : 0 < T.det := GaloisForLFunctions.HTGeometry.det_pos_of_quadForm_pos T hTpos
  -- the coefficient matrix
  have hxR : 1 / 2 < x₀ + R := by linarith
  set X := ‖xi (((1 / 2 + (x₀ + R) : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 with hX
  have hXpos : 0 < X := by
    rw [hX]; exact pow_pos (norm_pos_iff.mpr (xi_ne_zero_of_one_lt_re (by simp; linarith))) 2
  set C := X / (Real.pi * R ^ n) with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hentry : ∀ i j : Fin k, (Matrix.of fun i j : Fin k => (((n + i - j : ℕ).factorial : ℂ)⁻¹
      * iteratedDeriv (n + i - j) (xiSliceProduct t) (x₀ : ℂ)).re) i j
      = C * R ^ (j : ℕ) / R ^ (i : ℕ) * T i j := by
    intro i j
    have hji : (j : ℕ) ≤ n + i := by have := j.isLt; omega
    have hcast : (((n + i - j : ℕ) : ℝ) - n) = ((i : ℕ) : ℝ) - (j : ℕ) := by
      rw [Nat.cast_sub hji]; push_cast; ring
    have hf := congrArg Complex.re
      (iteratedDeriv_xiSliceProduct_eq_half_circle_freq t x₀ n (n + i - j) hR0 hxR)
    rw [Complex.ofReal_re, hcast] at hf
    rw [Matrix.of_apply, hf, scale_entry_eq hR0 hji]
    rfl
  rw [det_eq_pow_mul_det_of_diag_conj hR0 T _ hentry]
  exact mul_pos (pow_pos hCpos k) hTdet

theorem tendsto_rpow_mul_exp_neg_fifth_root (a : ℝ) :
    Filter.Tendsto (fun Λ : ℝ => Λ ^ a * Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8))
      Filter.atTop (nhds 0) := by
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 * a) (1 / 8) (by norm_num)).comp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5))
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with Λ hΛ
  simp only [Function.comp]
  rw [← Real.rpow_mul hΛ]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-- **The off-centre Toeplitz window.**  For every `k ≥ 1` and `0 < ε ≤ 1/8` there is `t₀ ≥ 1`
such that `det [a_{n+i−j}]_{i,j<k} > 0` for `a_m = g_t^{(m)}(x₀)/m!`, whenever `t ≥ t₀`,
`ε ≤ x₀ ≤ ½` and `n ≥ k − 1` with `(½ − x₀ + ε) log t ≤ n ≤ log t`. -/
theorem exists_xiSliceProduct_toeplitzDet_pos_offCentre (k : ℕ) (hk : 1 ≤ k) {ε : ℝ}
    (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ x₀ : ℝ, ε ≤ x₀ → x₀ ≤ 1 / 2 → ∀ n : ℕ, k - 1 ≤ n →
      (1 / 2 - x₀ + ε) * Real.log t ≤ n → (n : ℝ) ≤ Real.log t →
      0 < (Matrix.of fun i j : Fin k => (((n + i - j : ℕ).factorial : ℂ)⁻¹
        * iteratedDeriv (n + i - j) (xiSliceProduct t) (x₀ : ℂ)).re).det := by
  obtain ⟨cS, hcS, h₀, hh₀, hshort⟩ :=
    GaloisForLFunctions.HTGeometry.exists_integral_shortArcTrigPoly_sq_ge k hk
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = 2 * k - 1 := ⟨_, rfl⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 7 / 160 * cS / ((2 : ℝ) ^ N * (k : ℝ) ^ 2) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; positivity
  obtain ⟨η, hηdef⟩ : ∃ η, η = ε / 4 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; linarith
  have hη8 : η ≤ 1 / 8 := by rw [hηdef]; linarith
  obtain ⟨R₁, hR₁def⟩ : ∃ R₁ : ℝ, R₁ = 2 := ⟨_, rfl⟩
  have hR₁ : 1 ≤ R₁ := by rw [hR₁def]; norm_num
  have hR₁0 : 0 < R₁ := by linarith
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  obtain ⟨M, hMdef⟩ : ∃ M, M = Real.log 4 + Real.pi + 4 * E := ⟨_, rfl⟩
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hM0 : 0 < M := by rw [hMdef]; positivity
  obtain ⟨K, hKdef⟩ : ∃ K, K = R₁ / (2 * η) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hKdef, le_div_iff₀ (by positivity)]; linarith
  obtain ⟨θ₁, hθ₁def⟩ : ∃ θ₁, θ₁ = 1 / (1000 * K) := ⟨_, rfl⟩
  have hθ₁0 : 0 < θ₁ := by rw [hθ₁def]; positivity
  have hθ₁1 : θ₁ ≤ 1 := by
    rw [hθ₁def, div_le_one (by positivity)]; linarith only [hK1]
  obtain ⟨c, hcdef⟩ : ∃ c, c = 2 * η * θ₁ ^ 2 / 5 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hθsq : θ₁ ^ 2 ≤ 1 := pow_le_one₀ hθ₁0.le hθ₁1
  have hcη : c ≤ η := by
    rw [hcdef]
    have := mul_le_mul_of_nonneg_left hθsq (by linarith only [hη] : (0 : ℝ) ≤ 2 * η)
    linarith only [this, hη]
  obtain ⟨A, hA0, htail⟩ := exists_shiftArc_tail_le (R₁ := R₁) hη (by linarith)
  have e1 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_fifth_root (N / 2 : ℝ))).2 (500 * κ)
    (by positivity)
  have e6 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2))).2
    (2 * h₀) (by positivity)
  have e3 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5))).2 θ₁ hθ₁0
  have e4 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5))).2
    (3 / (2 * (1 + 128 * K))) (by positivity)
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp (e1.and (e3.and (e4.and e6)))
  have e5 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (N / 2 : ℝ) c hc0)).2
    (κ / (4 * Real.pi * A * R₁ ^ (N / 2 : ℝ))) (by positivity)
  obtain ⟨U₅, hU₅⟩ := Filter.eventually_atTop.mp e5
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hpi := Real.pi_pos
  have hRMη : 0 ≤ R₁ * M / η := by positivity
  have hEη : 0 ≤ E / η := by positivity
  have hΛ₀a := abs_nonneg Λ₀
  have hU₅a := abs_nonneg U₅
  have hΛη : 0 ≤ (|Λ₀| + 1) / (2 * η) := by positivity
  obtain ⟨L, hLdef⟩ : ∃ L, L = 32 * R₁ + 16 + (|Λ₀| + 1) / (2 * η)
      + 10 * (Real.log 2 + 2 * E + R₁ * M / η)
      + (Real.log (3 / 2) + Real.pi / 2 + 2 * E + R₁ * M / η) + E / η + |U₅| := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; linarith
  refine ⟨Real.exp L, Real.one_le_exp hL0, ?_⟩
  intro t ht x₀ hx₀ε hx₀2 n hnk hnlo hnhi
  have hx₀ : 0 ≤ x₀ := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos L) ht
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  rw [← hudef] at hnlo hnhi
  have hLu : L ≤ u := by
    rw [hudef, ← Real.log_exp L]; exact Real.log_le_log (Real.exp_pos L) ht
  have htu : u + 1 ≤ t := by
    have := Real.add_one_le_exp u
    rw [hudef, Real.exp_log ht0] at this; rw [hudef]; exact this
  rw [hLdef] at hLu
  have hu1 : 32 * R₁ + 16 ≤ u := by linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0]
  have hu2 : (|Λ₀| + 1) / (2 * η) ≤ u := by
    linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu3 : 10 * (Real.log 2 + 2 * E + R₁ * M / η) ≤ u := by
    linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu4 : Real.log (3 / 2) + Real.pi / 2 + 2 * E + R₁ * M / η ≤ u := by
    linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu5 : E / η ≤ u := by
    linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu6 : U₅ ≤ u := by
    have := le_abs_self U₅
    linarith only [this, hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu0 : 0 < u := by linarith only [hu1, hR₁0]
  have ht32 : 32 * R₁ + 16 ≤ t := by linarith only [hu1, htu]
  have ht8 : 8 ≤ t := by linarith only [ht32, hR₁0]
  have hR₁t : R₁ ≤ t / 2 := by linarith only [ht32, hR₁0]
  -- the saddle radius in `[½ + 2η − x₀, 3/2]`
  set a : ℝ := 1 / 2 + 2 * η - x₀ with ha
  have ha2η : 2 * η ≤ a := by rw [ha]; linarith
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  have hlo : a * (Real.log t + 2 * xiEulerConstant η) ≤ n := by
    rw [← hudef, ← hEdef]
    have h1 : 2 * η * (E / η) = 2 * E := by field_simp
    have h2 : 2 * η * (E / η) ≤ 2 * η * u := mul_le_mul_of_nonneg_left hu5 (by linarith)
    have h3 : a * (2 * E) ≤ 1 * (2 * E) := mul_le_mul_of_nonneg_right ha1 (by linarith)
    have h4 : (1 / 2 - x₀ + ε) * u = a * u + 2 * η * u := by rw [ha, hηdef]; ring
    have h5 : a * (u + 2 * E) = a * u + a * (2 * E) := by ring
    linarith only [h1, h2, h3, h4, h5, hnlo]
  have hhi : (n : ℝ) ≤ 3 / 2 * (Real.log (t / 2) - 2 * xiEulerConstant η) := by
    rw [Real.log_div ht0.ne' (by norm_num), ← hudef, ← hEdef]
    have h1 : 3 * (Real.log 2 + 2 * E) ≤ u := by linarith only [hu3, hRMη, hl2, hE0]
    linarith only [h1, hnhi]
  obtain ⟨R, ⟨hRa', hRb'⟩, hsad⟩ := exists_saddle_radius_shift (t := t) (n := n) hη ht8
    (by linarith only [ha, hη] : 1 / 2 + η ≤ x₀ + a) (by linarith only [ha2η, hη] : 0 ≤ a)
    (by linarith only [ha1] : a ≤ 3 / 2)
    (by linarith only [hx₀2, hR₁t, hR₁def] : x₀ + 3 / 2 ≤ t / 2) hlo hhi
  have hR0 : 0 < R := by linarith only [hRa', ha2η, hη]
  have hRa : 1 / 2 + 2 * η ≤ x₀ + R := by linarith only [hRa', ha]
  have hRb : x₀ + R ≤ R₁ := by linarith only [hRb', hx₀2, hR₁def]
  have hRt : x₀ + R ≤ t / 2 := le_trans hRb hR₁t
  have hRR₁ : R ≤ R₁ := by linarith only [hRb, hx₀]
  -- the slope
  obtain ⟨hF₁lo, hF₁hi⟩ := xiSliceShift_saddleSlope_bounds (t := t) (x₀ := x₀) (R := R) hη
    (by linarith only [hη8]) ht8 hR0 hRa hRt
  rw [← hEdef, ← hMdef] at hF₁lo hF₁hi
  have hRM : R * M / η ≤ R₁ * M / η :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRR₁ hM0.le) hη.le
  rw [Real.log_div ht0.ne' (by norm_num), ← hudef] at hF₁lo
  rw [← hudef] at hF₁hi
  have hF₁lo' : 9 / 10 * u ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re := by
    linarith only [hF₁lo, hRM, hu3]
  have hF₁hi' : (deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re ≤ 2 * u := by
    linarith only [hF₁hi, hRM, hu3, hl2, hRMη, hE0]
  -- the disc constant
  have hKd : xiSliceDiscConstantEuler η t R ≤ 2 * η * u := by
    unfold xiSliceDiscConstantEuler
    rw [← hEdef, ← hMdef]
    have e : Real.log (3 * t / 2) = Real.log (3 / 2) + u := by
      rw [show 3 * t / 2 = 3 / 2 * t by ring, Real.log_mul (by norm_num) ht0.ne', hudef]
    rw [e]
    have h1 : η * (R₁ * M / η) = R₁ * M := by field_simp
    have h2 := mul_le_mul_of_nonneg_left hu4 hη.le
    have h3 : R * M ≤ R₁ * M := mul_le_mul_of_nonneg_right hRR₁ hM0.le
    linarith only [h1, h2, h3]
  -- the tail on `[1/(1000K), π]`
  have htail' : ∀ θ : ℝ, 1 / (1000 * K) ≤ θ → θ ≤ Real.pi →
      ‖HTGeometry.saddleArc (xiSliceShift t x₀) R n θ‖ ≤ 2 * A * t ^ (-c) := by
    intro θ hθ hθπ
    rw [← hθ₁def] at hθ
    have hd := min_le_shift_decay (x₀ := x₀) hR0.le hθ₁0 hθ hθπ
    have h := htail t x₀ R θ _ n ht32 hx₀ hR0.le hRa hRb hd
    have hcd : c ≤ min (R * θ₁ ^ 2 / 5) (2 * x₀) := by
      refine le_min ?_ ?_
      · rw [hcdef]
        have h2R : 2 * η ≤ R := by linarith only [hRa', ha2η]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2R (sq_nonneg _))
          (by norm_num)
      · linarith only [hcη, hηdef, hx₀ε, hε]
    have h1 : t ^ (-min (R * θ₁ ^ 2 / 5) (2 * x₀)) ≤ t ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [ht8]) (by linarith only [hcd])
    have h2 : t ^ (-η) ≤ t ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [ht8]) (by linarith only [hcη])
    calc _ ≤ A * (t ^ (-η) + t ^ (-min (R * θ₁ ^ 2 / 5) (2 * x₀))) := h
      _ ≤ A * (t ^ (-c) + t ^ (-c)) :=
          mul_le_mul_of_nonneg_left (by linarith only [h1, h2]) hA0.le
      _ = 2 * A * t ^ (-c) := by ring
  -- the scale conditions
  have hΛlo : 2 * η * u ≤ R * u :=
    mul_le_mul_of_nonneg_right (by linarith only [hRa', ha2η]) hu0.le
  have hΛhi : R * u ≤ R₁ * u := mul_le_mul_of_nonneg_right hRR₁ hu0.le
  have hηu : |Λ₀| + 1 ≤ 2 * η * u := by
    have := hu2
    rw [div_le_iff₀ (by positivity)] at this
    linarith only [this]
  have hΛbig : max Λ₀ 1 ≤ R * u :=
    max_le (by have := le_abs_self Λ₀; linarith only [this, hΛlo, hηu])
      (by linarith only [hΛlo, hηu, hΛ₀a])
  obtain ⟨hE1, hE3, hE4, hE6⟩ := hΛ₀ (R * u) (le_trans (le_max_left _ _) hΛbig)
  rw [hθ₁def] at hE3
  have hΛpos : 0 < R * u := by linarith only [hΛbig, le_max_right Λ₀ 1]
  have hpowΛ : ((R * u) ^ (-(1 / 2) : ℝ) / 2) ^ (2 * k - 1)
      = (R * u) ^ (-(N / 2 : ℝ)) / 2 ^ N := by
    rw [← hNdef, div_pow, ← Real.rpow_natCast ((R * u) ^ (-(1 / 2) : ℝ)),
      ← Real.rpow_mul hΛpos.le]
    congr 2
    ring
  have hprodΛ : (R * u) ^ (N / 2 : ℝ) * (R * u) ^ (-(N / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hΛpos]; norm_num
  have hnegΛ : 0 < (R * u) ^ (-(N / 2 : ℝ)) := Real.rpow_pos_of_pos hΛpos _
  have hrhs : 7 / 160 * (cS * ((R * u) ^ (-(1 / 2) : ℝ) / 2) ^ (2 * k - 1) / (k : ℝ) ^ 2)
      = κ * (R * u) ^ (-(N / 2 : ℝ)) := by
    rw [hpowΛ, hκdef]
    field_simp
  have hmid : 2 * (1 / 1000 * Real.exp (-((R * u) ^ (1 / 5 : ℝ)) / 8))
      ≤ 7 / 160 * (cS * ((R * u) ^ (-(1 / 2) : ℝ) / 2) ^ (2 * k - 1) / (k : ℝ) ^ 2) := by
    rw [hrhs]
    have h1 : Real.exp (-((R * u) ^ (1 / 5 : ℝ)) / 8)
        = (R * u) ^ (N / 2 : ℝ) * Real.exp (-((R * u) ^ (1 / 5 : ℝ)) / 8)
          * (R * u) ^ (-(N / 2 : ℝ)) := by
      rw [mul_comm ((R * u) ^ (N / 2 : ℝ)), mul_assoc, hprodΛ, mul_one]
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_right hE1.le hnegΛ.le
    linarith only [h2]
  -- the tail at the scale `Λ^{−N/2}`
  have htailE : 2 * (Real.pi * (2 * A * t ^ (-c)))
      ≤ 7 / 160 * (cS * ((R * u) ^ (-(1 / 2) : ℝ) / 2) ^ (2 * k - 1) / (k : ℝ) ^ 2) := by
    rw [hrhs]
    have htc : t ^ (-c) = Real.exp (-c * u) := by
      rw [Real.rpow_def_of_pos ht0, hudef]; ring_nf
    have hpow : (R * u) ^ (N / 2 : ℝ) ≤ R₁ ^ (N / 2 : ℝ) * u ^ (N / 2 : ℝ) := by
      rw [← Real.mul_rpow hR₁0.le hu0.le]
      exact Real.rpow_le_rpow hΛpos.le hΛhi (by positivity)
    have h5 := (hU₅ u hu6).le
    have hR₁N : 0 < R₁ ^ (N / 2 : ℝ) := Real.rpow_pos_of_pos hR₁0 _
    have key : 4 * Real.pi * A * Real.exp (-c * u) * (R * u) ^ (N / 2 : ℝ) ≤ κ := by
      calc 4 * Real.pi * A * Real.exp (-c * u) * (R * u) ^ (N / 2 : ℝ)
          ≤ 4 * Real.pi * A * Real.exp (-c * u) * (R₁ ^ (N / 2 : ℝ) * u ^ (N / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = 4 * Real.pi * A * R₁ ^ (N / 2 : ℝ) * (u ^ (N / 2 : ℝ) * Real.exp (-c * u)) := by ring
        _ ≤ 4 * Real.pi * A * R₁ ^ (N / 2 : ℝ) * (κ / (4 * Real.pi * A * R₁ ^ (N / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = κ := by field_simp
    rw [htc]
    have h3 := mul_le_mul_of_nonneg_right key hnegΛ.le
    have e : 4 * Real.pi * A * Real.exp (-c * u) * (R * u) ^ (N / 2 : ℝ) * (R * u) ^ (-(N / 2 : ℝ))
        = 2 * (Real.pi * (2 * A * Real.exp (-c * u))) := by
      rw [mul_assoc (4 * Real.pi * A * Real.exp (-c * u)), hprodΛ]; ring
    linarith
  exact xiSliceProduct_toeplitzDet_pos_of_saddle_shift hk hnk hη hη8 hR₁ hKdef ht8 hu0 hx₀ hR0
    hRa hRb hRt hsad hF₁lo' hF₁hi' hKd htail' (le_trans (le_max_right _ _) hΛbig) hE3 hE4 hcS
    hshort (by linarith only [hE6.le]) hmid htailE

end

end RHTower
