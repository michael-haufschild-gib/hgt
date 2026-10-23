import GaloisForLFunctions.TransHorizonIncidenceMechanics.OscillatingPrimePatternsReadTheCriticalZeros

/-!
# Oscillating prime patterns are paid exactly at the critical zeros

At amplitude `a = 1` and frequency `t₀ ≠ 0` the pattern `f(p) = cos(t₀ log p)` sits on the quarter
threshold at the height `t₀`: with `s = 1/2 + u + it`, `s₀ = 1/2 + it₀`,
`|C(s)|² ≍ |ζ(1 + u + i(t − t₀))| ≍ 1/|s − s₀|` near `s₀`. The boundary line energy weighs this
borderline singularity with `|ζ(s)|²`:

* if `ζ(s₀) ≠ 0`, the line integrand is `≥ κ/(u + |t − t₀|) − C'` near `t₀`, the line energy grows like
  `κ log(1/u)`, and a bounded receiver (which caps it by `4πE`) is impossible
  (`not_receiverBounded_oscWeight_one`);
* if `ζ(s₀) = 0`, then `|ζ(s)| ≤ L|s − s₀|` cancels the singularity, the integrand is bounded near
  `t₀`, and the receiver is paid (`receiverBounded_oscWeight_one_of_zero`).

With the paid range of `OscillatingPrimePatternsReadTheCriticalZeros` this is the complete phase
diagram (`receiverBounded_oscWeight_iff`): for `a ∈ [−1, 1]` and `t₀ ∈ ℝ`, the weight
`f_{a,t₀}(d) d^{-1/2}` is paid iff `t₀ = 0 ∧ a < 1/2`, or `t₀ ≠ 0 ∧ (a < 1 ∨ ζ(1/2 + it₀) = 0)`.
At `t₀ = 0` the two singular heights merge and the threshold of the amplitude halves. The
half-damped receiver of `cos(t₀ log p)` is paid exactly when `1/2 + it₀` is a zero of `ζ`.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Local behaviour of `ζ` -/

/-- `ζ` is Lipschitz near every point `s₀ ≠ 1`: a derivative bound on a closed ball. -/
theorem exists_norm_zeta_sub_le {s₀ : ℂ} (hs₀ : s₀ ≠ 1) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ s : ℂ, ‖s - s₀‖ ≤ r →
      ‖riemannZeta s - riemannZeta s₀‖ ≤ L * ‖s - s₀‖ := by
  have hpos : 0 < ‖s₀ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs₀)
  set r : ℝ := ‖s₀ - 1‖ / 2
  have hr : 0 < r := by positivity
  have hB1 : ∀ z ∈ Metric.closedBall s₀ r, z ≠ 1 := by
    intro z hz h
    rw [h, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] at hz
    simp only [r] at hz
    linarith
  have hdiff : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hcont : ContinuousOn (deriv riemannZeta) (Metric.closedBall s₀ r) := fun z hz =>
    (hdiff.analyticAt (isOpen_compl_singleton.mem_nhds (hB1 z hz))).deriv.continuousAt.continuousWithinAt
  obtain ⟨L, hL⟩ := (isCompact_closedBall s₀ r).exists_bound_of_continuousOn hcont
  refine ⟨r, max L 0, hr, le_max_right _ _, fun s hs => ?_⟩
  have hmem : s ∈ Metric.closedBall s₀ r := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hs
  exact (convex_closedBall s₀ r).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => differentiableAt_riemannZeta (hB1 z hz))
    (fun z hz => (hL z hz).trans (le_max_left _ _)) (Metric.mem_closedBall_self hr.le) hmem

/-- Near a point `s₀ ≠ 1` with `ζ(s₀) ≠ 0`, `|ζ| > |ζ(s₀)|/2`. -/
theorem exists_norm_zeta_gt_near {s₀ : ℂ} (hs₀ : s₀ ≠ 1) (hz : riemannZeta s₀ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ s : ℂ, ‖s - s₀‖ < r → ‖riemannZeta s₀‖ / 2 < ‖riemannZeta s‖ := by
  have hc : ContinuousAt riemannZeta s₀ := (differentiableAt_riemannZeta hs₀).continuousAt
  have hlt : ‖riemannZeta s₀‖ / 2 < ‖riemannZeta s₀‖ := by
    have := norm_pos_iff.mpr hz; linarith
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (Filter.Tendsto.eventually hc.norm (lt_mem_nhds hlt))
  exact ⟨r, hr, fun s hs => hball (by rwa [dist_eq_norm])⟩

/-- `(x^{1/2})² = x` for `x ≥ 0`. -/
theorem rpow_half_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-! ### A critical zero pays the boundary -/

/-- **A zero on the critical line pays the boundary pattern.** If `t₀ > 0` and
`ζ(1/2 + it₀) = 0`, the half-damped weight of `f(p) = cos(t₀ log p)` has bounded receiver. -/
theorem receiverBounded_oscWeight_one_of_zero {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hz : riemannZeta (1 / 2 + t₀ * I) = 0) : ReceiverBounded (oscWeight 1 t₀) := by
  have hs₀1 : (1 / 2 + t₀ * I : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  obtain ⟨r, L, hr, hL, hLip⟩ := exists_norm_zeta_sub_le hs₀1
  obtain ⟨B, hB0, hBs⟩ := exists_norm_oscSeries_le_small (a := 1) zero_le_one le_rfl ht₀
  set T : ℝ := 2 * t₀ + 2
  have hT : 2 ≤ T := by simp only [T]; linarith
  obtain ⟨Z₀, hZ₀, hZ⟩ := exists_norm_zeta_le_on_tall_box T
  set P : ℝ := ∑' d : ℕ, oscWeight 1 t₀ d / d
  set E2 : ℝ := Real.exp (2 * primeSquareMass)
  have hE2 : 0 < E2 := Real.exp_pos _
  have hA0 : 0 ≤ 4 * (2 * L ^ 2 * B ^ 2 * r + 2 * L ^ 2 * P ^ 2 * r ^ 2 +
      Z₀ ^ 2 * (2 * (B ^ 2 * r⁻¹) + 2 * P ^ 2)) := by positivity
  set A : ℝ := 4 * (2 * L ^ 2 * B ^ 2 * r + 2 * L ^ 2 * P ^ 2 * r ^ 2 +
      Z₀ ^ 2 * (2 * (B ^ 2 * r⁻¹) + 2 * P ^ 2))
  have hwre : ∀ σ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).re = σ + 1 / 2 := fun σ t => by simp
  have hwim : ∀ σ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).im = t := fun σ t => by simp
  have hsmall : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < t → t ≤ T → t ≠ t₀ →
      lineIntegrand (oscWeight 1 t₀) P σ t ≤ (fun _ : ℝ => A) t := by
    intro σ t hσ hσ' ht htT _
    have hF := hBs ((σ : ℂ) + t * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim]; exact ht) (by rw [hwim]; exact htT)
    have hd_eq : (σ : ℂ) + t * I + 1 / 2 - t₀ * I - 1 = (σ : ℂ) + t * I - (1 / 2 + t₀ * I) := by
      ring
    rw [hd_eq] at hF
    have hdre : ((σ : ℂ) + t * I - (1 / 2 + t₀ * I)).re = σ - 1 / 2 := by simp
    have hd0 : 0 < ‖(σ : ℂ) + t * I - (1 / 2 + t₀ * I)‖ := by
      have := Complex.abs_re_le_norm ((σ : ℂ) + t * I - (1 / 2 + t₀ * I))
      rw [hdre, abs_of_pos (by linarith)] at this
      linarith
    set d := ‖(σ : ℂ) + t * I - (1 / 2 + t₀ * I)‖ with hd_def
    have hC : ‖weightDirichletSeries (oscWeight 1 t₀) ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤
        B * d ^ (-(1 / 2 : ℝ)) + |P| := by
      rw [weightDirichletSeries_oscWeight]
      refine (norm_sub_le _ _).trans (add_le_add hF (by rw [Complex.norm_real, Real.norm_eq_abs]))
    have hpw : (d ^ (-(1 / 2 : ℝ))) ^ 2 = d⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd0.le,
        show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    have hsq : ‖weightDirichletSeries (oscWeight 1 t₀) ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2 ≤
        2 * (B ^ 2 * d⁻¹) + 2 * P ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) hC 2
      have hab : ∀ x y : ℝ, (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := fun x y => by
        nlinarith [sq_nonneg (x - y)]
      refine h.trans ((hab _ _).trans (le_of_eq ?_))
      rw [mul_pow, hpw, sq_abs]
    have hsn : σ ≤ ‖(σ : ℂ) + t * I‖ := by
      have := Complex.abs_re_le_norm ((σ : ℂ) + t * I)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at this
      linarith [le_abs_self σ]
    have hs2 : (1 / 2 : ℝ) ^ 2 ≤ ‖(σ : ℂ) + t * I‖ ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hden : 0 < ‖(σ : ℂ) + t * I‖ ^ 2 := lt_of_lt_of_le (by norm_num) hs2
    have hnum : ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 *
        ‖weightDirichletSeries (oscWeight 1 t₀) ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2 ≤ A / 4 := by
      have hrest : 0 ≤ Z₀ ^ 2 * (2 * (B ^ 2 * r⁻¹) + 2 * P ^ 2) := by positivity
      have hnear : 0 ≤ 2 * L ^ 2 * B ^ 2 * r + 2 * L ^ 2 * P ^ 2 * r ^ 2 := by positivity
      rcases le_or_gt d r with hdr | hdr
      · -- near the zero: `|ζ(s)| ≤ L |s − s₀|`
        have hζ : ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ L * d := by
          have := hLip ((σ : ℂ) + t * I) hdr
          rwa [hz, sub_zero] at this
        have hζ2 : ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤ L ^ 2 * d ^ 2 := by
          have := pow_le_pow_left₀ (norm_nonneg _) hζ 2; rwa [mul_pow] at this
        calc ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 *
              ‖weightDirichletSeries (oscWeight 1 t₀) ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2
            ≤ L ^ 2 * d ^ 2 * (2 * (B ^ 2 * d⁻¹) + 2 * P ^ 2) :=
              mul_le_mul hζ2 hsq (sq_nonneg _) (by positivity)
          _ = 2 * L ^ 2 * B ^ 2 * d + 2 * L ^ 2 * P ^ 2 * d ^ 2 := by
              field_simp
          _ ≤ 2 * L ^ 2 * B ^ 2 * r + 2 * L ^ 2 * P ^ 2 * r ^ 2 :=
              add_le_add (mul_le_mul_of_nonneg_left hdr (by positivity))
                (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd0.le hdr 2) (by positivity))
          _ ≤ A / 4 := by simp only [A]; linarith
      · -- away from it: `|ζ(s)| ≤ Z₀`
        have hdinv : d⁻¹ ≤ r⁻¹ := inv_anti₀ hr hdr.le
        have hζ2 : ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤ Z₀ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _)
            (hZ σ t hσ.le hσ'.le (by rw [abs_of_pos ht]; exact htT)) 2
        have hsq' := hsq.trans (show 2 * (B ^ 2 * d⁻¹) + 2 * P ^ 2 ≤
            2 * (B ^ 2 * r⁻¹) + 2 * P ^ 2 by
          have := mul_le_mul_of_nonneg_left hdinv (sq_nonneg B); linarith)
        calc ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 *
              ‖weightDirichletSeries (oscWeight 1 t₀) ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2
            ≤ Z₀ ^ 2 * (2 * (B ^ 2 * r⁻¹) + 2 * P ^ 2) :=
              mul_le_mul hζ2 hsq' (sq_nonneg _) (sq_nonneg _)
          _ ≤ A / 4 := by simp only [A]; linarith
    show lineIntegrand (oscWeight 1 t₀) P σ t ≤ A
    simp only [lineIntegrand, norm_div, norm_mul, div_pow, mul_pow]
    rw [div_le_iff₀ hden]
    calc _ ≤ A / 4 := hnum
      _ = A * (1 / 2) ^ 2 := by ring
      _ ≤ A * ‖(σ : ℂ) + t * I‖ ^ 2 := mul_le_mul_of_nonneg_left hs2 hA0
  have hlarge : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → T < t →
      ‖weightDirichletSeries (oscWeight 1 t₀) ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤
        (10 * E2 + |P|) * t ^ (1 / 4 : ℝ) := by
    intro σ t hσ hσ' ht
    rw [weightDirichletSeries_oscWeight]
    refine (norm_sub_le _ _).trans ?_
    have h := norm_oscSeries_le_large zero_le_one le_rfl ht₀ (w := (σ : ℂ) + t * I + 1 / 2)
      (by rw [hwre]; linarith) (by rw [hwre]; linarith) (by rw [hwim]; exact ht)
    rw [hwim] at h
    have h1 : 1 ≤ t ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg P]
  have hg : IntegrableOn (fun _ : ℝ => A) (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp intervalIntegrable_const
  obtain ⟨M, hM⟩ := exists_lineEnergy_le_of_majorant (g := fun _ : ℝ => A) hT hg hsmall hlarge
  exact ⟨3 * M / (4 * Real.pi),
    weightPronicEnergy_le_of_lineEnergy_le (dampedClass_oscWeight (by norm_num) t₀) hM⟩

/-! ### A nonzero critical value leaves the boundary unpaid -/

/-- The closing algebra of the lower bound: `|ζ(s)| ≥ c₀`, `0 < |s| ≤ S₁`, `P²/2 − m² ≤ Y²` and
`K ≤ P²` give `(c₀/S₁)²(K/2 − m²) ≤ (|ζ(s)| Y/|s|)²`. -/
theorem sq_div_ge_of_bounds {Z Y s c₀ S₁ Pn m K : ℝ} (hc₀ : 0 < c₀) (hZ : c₀ ≤ Z) (hs0 : 0 < s)
    (hs1 : s ≤ S₁) (hY : 0 ≤ Y) (hYP : Pn ^ 2 / 2 - m ^ 2 ≤ Y ^ 2) (hP : K ≤ Pn ^ 2) :
    (c₀ / S₁) ^ 2 * (K / 2 - m ^ 2) ≤ (Z * Y / s) ^ 2 := by
  have hS₁ : 0 < S₁ := lt_of_lt_of_le hs0 hs1
  have hlow : c₀ * Y / S₁ ≤ Z * Y / s := by
    rw [div_le_div_iff₀ hS₁ hs0]
    have h := mul_le_mul hZ hs1 hs0.le (hc₀.le.trans hZ)
    nlinarith [mul_le_mul_of_nonneg_right h hY]
  have hsq := pow_le_pow_left₀ (by positivity) hlow 2
  have e1 : (c₀ * Y / S₁) ^ 2 = (c₀ / S₁) ^ 2 * Y ^ 2 := by ring
  have h3 : K / 2 - m ^ 2 ≤ Y ^ 2 := by linarith
  have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg (c₀ / S₁))
  rw [e1] at hsq
  linarith

/-- **The pointwise lower bound at `s = 1/2 + u + i(t₀ + τ)`**, given the local bounds on `ζ` near the
pole, near `s₀ = 1/2 + it₀` and near `1 + 2it₀`: with `c₀ = |ζ(s₀)|/2`, `c_q = |ζ(1 + 2it₀)|/2`,
`S₁ = |s₀| + 1`, the line integrand is `≥ (c₀/S₁)² (e^{-4S} c_q/(4(u + τ)) − m²)`. -/
theorem lineIntegrand_oscWeight_one_ge_of {t₀ ρ r₀ rq u τ : ℝ}
    (hζ1 : ∀ w : ℂ, w ≠ 1 → ‖w - 1‖ < ρ → 1 / (2 * ‖w - 1‖) ≤ ‖riemannZeta w‖)
    (hζ0 : ∀ s : ℂ, ‖s - (1 / 2 + t₀ * I)‖ < r₀ →
      ‖riemannZeta (1 / 2 + t₀ * I)‖ / 2 < ‖riemannZeta s‖)
    (hζp : ∀ s : ℂ, ‖s - (1 + 2 * t₀ * I)‖ < rq →
      ‖riemannZeta (1 + 2 * t₀ * I)‖ / 2 < ‖riemannZeta s‖)
    (hc₀ : 0 < ‖riemannZeta (1 / 2 + t₀ * I)‖) (hcq : 0 < ‖riemannZeta (1 + 2 * t₀ * I)‖)
    (hu : 0 < u) (hτ : 0 ≤ τ) (hρ : u + τ < ρ) (h0 : u + τ < r₀) (hq : u + τ < rq)
    (h1 : u + τ ≤ 1) :
    ((‖riemannZeta (1 / 2 + t₀ * I)‖ / 2) / (‖(1 / 2 + t₀ * I : ℂ)‖ + 1)) ^ 2 *
        (Real.exp (-(4 * primeSquareMass)) *
            (‖riemannZeta (1 + 2 * t₀ * I)‖ / 2 / (2 * (u + τ))) / 2 -
          (∑' d : ℕ, oscWeight 1 t₀ d / d) ^ 2) ≤
      lineIntegrand (oscWeight 1 t₀) (∑' d : ℕ, oscWeight 1 t₀ d / d) (1 / 2 + u) (t₀ + τ) := by
  set m : ℝ := ∑' d : ℕ, oscWeight 1 t₀ d / d
  set S := primeSquareMass
  set s : ℂ := (((1 / 2 + u : ℝ)) : ℂ) + ((t₀ + τ : ℝ) : ℂ) * I
  have hss₀ : s - (1 / 2 + t₀ * I) = (u : ℂ) + τ * I := by simp only [s]; push_cast; ring
  have hnorm_ut : ‖(u : ℂ) + τ * I‖ ≤ u + τ := by
    have := Complex.norm_le_abs_re_add_abs_im ((u : ℂ) + τ * I)
    simpa [abs_of_pos hu, abs_of_nonneg hτ] using this
  have hnorm_ut0 : u ≤ ‖(u : ℂ) + τ * I‖ := by
    have := Complex.abs_re_le_norm ((u : ℂ) + τ * I)
    simpa [abs_of_pos hu] using this
  have hut : 0 < u + τ := by linarith
  -- `|ζ(s)| > c₀` and `0 < |s| ≤ S₁`
  have hζs := hζ0 s (by rw [hss₀]; linarith)
  have hs1 : ‖s‖ ≤ ‖(1 / 2 + t₀ * I : ℂ)‖ + 1 := by
    have h : ‖s‖ ≤ ‖(1 / 2 + t₀ * I : ℂ)‖ + ‖s - (1 / 2 + t₀ * I)‖ := by
      calc ‖s‖ = ‖(1 / 2 + t₀ * I : ℂ) + (s - (1 / 2 + t₀ * I))‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    rw [hss₀] at h
    linarith
  have hsre : s.re = 1 / 2 + u := by simp [s]
  have hs0 : 0 < ‖s‖ := by
    have := Complex.abs_re_le_norm s
    rw [hsre, abs_of_pos (by linarith)] at this
    linarith
  -- the two `ζ` factors of the series at `w = s + 1/2`
  have hwre : 1 < (s + 1 / 2).re := by rw [Complex.add_re, hsre]; norm_num; linarith
  have hwm : s + 1 / 2 - t₀ * I - 1 = (u : ℂ) + τ * I := by rw [← hss₀]; ring
  have hwp : s + 1 / 2 + t₀ * I - (1 + 2 * t₀ * I) = (u : ℂ) + τ * I := by rw [← hss₀]; ring
  have hwm1 : s + 1 / 2 - t₀ * I ≠ 1 := by
    intro h
    have h0 : s + 1 / 2 - t₀ * I - 1 = 0 := by rw [h, sub_self]
    rw [hwm] at h0
    rw [h0, norm_zero] at hnorm_ut0
    linarith
  have hZm : 1 / (2 * (u + τ)) ≤ ‖riemannZeta (s + 1 / 2 - t₀ * I)‖ := by
    have h := hζ1 (s + 1 / 2 - t₀ * I) hwm1 (by rw [hwm]; linarith)
    rw [hwm] at h
    exact le_trans (one_div_le_one_div_of_le (by linarith) (by linarith)) h
  have hZp := hζp (s + 1 / 2 + t₀ * I) (by rw [hwp]; linarith)
  have hprod : ‖riemannZeta (1 + 2 * t₀ * I)‖ / 2 / (2 * (u + τ)) ≤
      ‖riemannZeta (s + 1 / 2 - t₀ * I)‖ * ‖riemannZeta (s + 1 / 2 + t₀ * I)‖ := by
    calc ‖riemannZeta (1 + 2 * t₀ * I)‖ / 2 / (2 * (u + τ))
        = 1 / (2 * (u + τ)) * (‖riemannZeta (1 + 2 * t₀ * I)‖ / 2) := by ring
      _ ≤ _ := mul_le_mul hZm hZp.le (by positivity) (norm_nonneg _)
  -- `|C(s)|² ≥ e^{-4S} |ζ(w − it₀)| |ζ(w + it₀)|`
  have hP := (norm_oscSeries_le_ge (a := 1) (by norm_num) t₀ hwre).2
  set Pn := ‖∑' n : ℕ, (oscPattern 1 t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-(s + 1 / 2))‖
  have hP2 : Real.exp (-(4 * S)) * (‖riemannZeta (1 + 2 * t₀ * I)‖ / 2 / (2 * (u + τ))) ≤
      Pn ^ 2 := by
    have h0 : 0 ≤ Real.exp (-(2 * S)) * (‖riemannZeta (s + 1 / 2 - t₀ * I)‖ *
        ‖riemannZeta (s + 1 / 2 + t₀ * I)‖) ^ (1 / 2 : ℝ) := by positivity
    have h := pow_le_pow_left₀ h0 hP 2
    rw [mul_pow, rpow_half_sq (by positivity), ← Real.exp_nat_mul,
      show ((2 : ℕ) : ℝ) * -(2 * S) = -(4 * S) by push_cast; ring] at h
    exact le_trans (mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le) h
  -- `|C(s) − m|² ≥ |C(s)|²/2 − m²`
  set Y := ‖weightDirichletSeries (oscWeight 1 t₀) s - (m : ℂ)‖
  have hPY : Pn ≤ Y + |m| := by
    have h := norm_sub_norm_le (weightDirichletSeries (oscWeight 1 t₀) s) (m : ℂ)
    have hW : ‖weightDirichletSeries (oscWeight 1 t₀) s‖ = Pn := by
      rw [weightDirichletSeries_oscWeight]
    rw [hW, Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hYP : Pn ^ 2 / 2 - m ^ 2 ≤ Y ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hPY 2
    nlinarith [sq_nonneg (Y - |m|), sq_abs m]
  have hint : lineIntegrand (oscWeight 1 t₀) m (1 / 2 + u) (t₀ + τ) =
      (‖riemannZeta s‖ * Y / ‖s‖) ^ 2 := by
    simp only [lineIntegrand, norm_div, norm_mul]
    rfl
  rw [hint]
  exact sq_div_ge_of_bounds (by positivity) hζs.le hs0 hs1 hY0 hYP hP2

/-- **Off-axis lower bound at a nonzero critical value.** If `t₀ > 0` and `ζ(1/2 + it₀) ≠ 0`, there
are `r, κ > 0` and `C'` with `κ/(u + τ) − C' ≤` the line integrand of `cos(t₀ log p)` at
`s = 1/2 + u + i(t₀ + τ)`, for `0 < u ≤ r`, `0 ≤ τ ≤ r`. -/
theorem exists_lineIntegrand_oscWeight_one_ge {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hz : riemannZeta (1 / 2 + t₀ * I) ≠ 0) :
    ∃ r κ C' : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ 0 < κ ∧ ∀ u τ : ℝ, 0 < u → u ≤ r → 0 ≤ τ → τ ≤ r →
      κ / (u + τ) - C' ≤ lineIntegrand (oscWeight 1 t₀) (∑' d : ℕ, oscWeight 1 t₀ d / d)
        (1 / 2 + u) (t₀ + τ) := by
  have hs₀1 : (1 / 2 + t₀ * I : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  have hq1 : (1 + 2 * t₀ * I : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.im h; norm_num at this; linarith
  have hqz : riemannZeta (1 + 2 * t₀ * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num)
  obtain ⟨ρ, hρ, hζ1⟩ := exists_norm_zeta_ge_near_one
  obtain ⟨r₀, hr₀, hζ0⟩ := exists_norm_zeta_gt_near hs₀1 hz
  obtain ⟨rq, hrq, hζp⟩ := exists_norm_zeta_gt_near hq1 hqz
  have hc₀ := norm_pos_iff.mpr hz
  have hcq := norm_pos_iff.mpr hqz
  have hmin : 0 < min (min ρ r₀) rq := lt_min (lt_min hρ hr₀) hrq
  set r : ℝ := min (min (min ρ r₀) rq / 4) (1 / 4)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hr4 : r ≤ 1 / 4 := min_le_right _ _
  have hr' : 2 * r < min (min ρ r₀) rq := by
    have := min_le_left (min (min ρ r₀) rq / 4) (1 / 4)
    linarith
  have hrρ : 2 * r < ρ := lt_of_lt_of_le hr' ((min_le_left _ _).trans (min_le_left _ _))
  have hr0 : 2 * r < r₀ := lt_of_lt_of_le hr' ((min_le_left _ _).trans (min_le_right _ _))
  have hrp : 2 * r < rq := lt_of_lt_of_le hr' (min_le_right _ _)
  set A : ℝ := ((‖riemannZeta (1 / 2 + t₀ * I)‖ / 2) / (‖(1 / 2 + t₀ * I : ℂ)‖ + 1)) ^ 2
  have hA : 0 < A := by positivity
  refine ⟨r, A * Real.exp (-(4 * primeSquareMass)) * (‖riemannZeta (1 + 2 * t₀ * I)‖ / 2) / 4,
    A * (∑' d : ℕ, oscWeight 1 t₀ d / d) ^ 2, hr, hr4, by positivity,
    fun u τ hu hur hτ hτr => ?_⟩
  have h := lineIntegrand_oscWeight_one_ge_of hζ1 hζ0 hζp hc₀ hcq hu hτ (by linarith)
    (by linarith) (by linarith) (by linarith)
  refine le_trans (le_of_eq ?_) h
  have hut : u + τ ≠ 0 := by linarith
  have hS : ‖(1 / 2 + t₀ * I : ℂ)‖ + 1 ≠ 0 := by positivity
  simp only [A]
  field_simp
  ring

/-- **A nonzero critical value leaves the boundary pattern unpaid.** If `t₀ > 0` and
`ζ(1/2 + it₀) ≠ 0`, the half-damped weight of `f(p) = cos(t₀ log p)` has unbounded receiver: its
line energy at `σ = 1/2 + u` exceeds `κ log(1/u) − O(1)`, while a bounded receiver caps it by `4πE`. -/
theorem not_receiverBounded_oscWeight_one {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hz : riemannZeta (1 / 2 + t₀ * I) ≠ 0) : ¬ ReceiverBounded (oscWeight 1 t₀) := by
  rintro ⟨E, hE⟩
  set c := oscWeight 1 t₀
  have hc : DampedClass 1 (1 / 2) c := dampedClass_oscWeight (by norm_num) t₀
  set m : ℝ := ∑' d : ℕ, c d / d
  obtain ⟨r, κ, C', hr, hr4, hκ, hpt⟩ := exists_lineIntegrand_oscWeight_one_ge ht₀ hz
  have hE0 : 0 ≤ E := by simpa [weightPronicEnergy] using hE 0
  -- a paid receiver caps every line energy by `4πE`
  have hup : ∀ u : ℝ, 0 < u → u ≤ r → ∫ t, lineIntegrand c m (1 / 2 + u) t ≤ 4 * Real.pi * E := by
    intro u hu hur
    have hσ : 1 / 2 < 1 / 2 + u := by linarith
    have hσ1 : 1 / 2 + u < 1 := by linarith
    have hid := sum_sq_mul_mellinCell_eq_lineEnergy hc hσ hσ1
    have hcap := tsum_sq_mul_mellinCell_le_of_energy (weightCenteredPrefix_zero c m) hσ.le hE
    have h : (1 / 2 + u) / Real.pi * ∫ t, lineIntegrand c m (1 / 2 + u) t ≤ 4 * (1 / 2 + u) * E :=
      hid.symm.le.trans hcap
    have hpi := Real.pi_pos
    rw [div_mul_eq_mul_div, div_le_iff₀ hpi] at h
    nlinarith
  -- the segment `t₀ ≤ t ≤ t₀ + r` carries `κ log((u + r)/u) − C' r`
  have hlow : ∀ u : ℝ, 0 < u → u ≤ r →
      κ * Real.log ((u + r) / u) - C' * r ≤ ∫ t, lineIntegrand c m (1 / 2 + u) t := by
    intro u hu hur
    have hσ : 1 / 2 < 1 / 2 + u := by linarith
    have hσ1 : 1 / 2 + u < 1 := by linarith
    have hfi : Integrable (lineIntegrand c m (1 / 2 + u)) := integrable_lineEnergy hc hσ hσ1
    have hf0 : 0 ≤ᵐ[volume] lineIntegrand c m (1 / 2 + u) :=
      Eventually.of_forall fun t => by simp only [Pi.zero_apply, lineIntegrand]; positivity
    have hinv : IntervalIntegrable (fun τ : ℝ => (u + τ)⁻¹) volume 0 r := by
      refine ContinuousOn.intervalIntegrable ((continuousOn_const.add continuousOn_id).inv₀ ?_)
      intro τ hτ
      rw [uIcc_of_le hr.le] at hτ
      have : 0 < u + τ := by linarith [hτ.1]
      exact this.ne'
    have hg : IntervalIntegrable (fun τ : ℝ => κ * (u + τ)⁻¹ - C') volume 0 r :=
      (hinv.const_mul κ).sub intervalIntegrable_const
    have hval : ∫ τ in (0 : ℝ)..r, (κ * (u + τ)⁻¹ - C') =
        κ * Real.log ((u + r) / u) - C' * r := by
      rw [intervalIntegral.integral_sub (hinv.const_mul κ) intervalIntegrable_const,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_add_left (fun x => x⁻¹), add_zero,
        integral_inv_of_pos hu (by linarith), intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hfs : IntervalIntegrable (fun τ => lineIntegrand c m (1 / 2 + u) (t₀ + τ)) volume 0 r :=
      (hfi.comp_add_left t₀).intervalIntegrable
    have hshift : ∫ τ in (0 : ℝ)..r, lineIntegrand c m (1 / 2 + u) (t₀ + τ) =
        ∫ t in t₀..t₀ + r, lineIntegrand c m (1 / 2 + u) t := by
      rw [intervalIntegral.integral_comp_add_left (fun t => lineIntegrand c m (1 / 2 + u) t) t₀,
        add_zero]
    calc κ * Real.log ((u + r) / u) - C' * r
        = ∫ τ in (0 : ℝ)..r, (κ * (u + τ)⁻¹ - C') := hval.symm
      _ ≤ ∫ τ in (0 : ℝ)..r, lineIntegrand c m (1 / 2 + u) (t₀ + τ) :=
          intervalIntegral.integral_mono_on hr.le hg hfs fun τ hτ => by
            have := hpt u τ hu hur hτ.1 hτ.2
            rwa [div_eq_mul_inv] at this
      _ = ∫ t in t₀..t₀ + r, lineIntegrand c m (1 / 2 + u) t := hshift
      _ = ∫ t in Ioc t₀ (t₀ + r), lineIntegrand c m (1 / 2 + u) t :=
          intervalIntegral.integral_of_le (by linarith)
      _ ≤ ∫ t, lineIntegrand c m (1 / 2 + u) t := setIntegral_le_integral hfi hf0
  -- choose `u = r e^{-X}` with `κ X > 4πE + C' r`
  set X : ℝ := (4 * Real.pi * E + |C'| * r + 1) / κ
  have hX : 0 < X := by
    have := Real.pi_pos
    positivity
  set u : ℝ := r * Real.exp (-X)
  have hu : 0 < u := by positivity
  have hur : u ≤ r := mul_le_of_le_one_right hr.le (Real.exp_le_one_iff.mpr (by linarith))
  have hlog : X ≤ Real.log ((u + r) / u) := by
    have hru : r / u = Real.exp X := by
      simp only [u]
      rw [div_mul_eq_div_div, div_self hr.ne', one_div, ← Real.exp_neg, neg_neg]
    calc X = Real.log (r / u) := by rw [hru, Real.log_exp]
      _ ≤ Real.log ((u + r) / u) :=
          Real.log_le_log (div_pos hr hu) (div_le_div_of_nonneg_right (by linarith) hu.le)
  have h1 := hlow u hu hur
  have h2 := hup u hu hur
  have hκX : κ * X = 4 * Real.pi * E + |C'| * r + 1 := by
    simp only [X]; field_simp
  have hC'r : C' * r ≤ |C'| * r := mul_le_mul_of_nonneg_right (le_abs_self C') hr.le
  nlinarith [mul_le_mul_of_nonneg_left hlog hκ.le]

/-! ### The phase diagram -/

/-- The critical values at `±t₀` vanish together (`ζ(s̄) = conj ζ(s)`). -/
theorem riemannZeta_half_add_neg_eq_zero_iff (t₀ : ℝ) :
    riemannZeta (1 / 2 + ((-t₀ : ℝ) : ℂ) * I) = 0 ↔ riemannZeta (1 / 2 + t₀ * I) = 0 := by
  have h : (1 / 2 + ((-t₀ : ℝ) : ℂ) * I) = starRingEnd ℂ (1 / 2 + t₀ * I) := by
    apply Complex.ext <;> simp
  rw [h, riemannZeta_conj, map_eq_zero]

/-- **The boundary pattern detects the critical zeros.** For `t₀ ≠ 0`, the half-damped weight of
`f(p) = cos(t₀ log p)` has bounded receiver iff `ζ(1/2 + it₀) = 0`. -/
theorem receiverBounded_oscWeight_one_iff {t₀ : ℝ} (ht₀ : t₀ ≠ 0) :
    ReceiverBounded (oscWeight 1 t₀) ↔ riemannZeta (1 / 2 + t₀ * I) = 0 := by
  have key : ∀ t : ℝ, 0 < t →
      (ReceiverBounded (oscWeight 1 t) ↔ riemannZeta (1 / 2 + t * I) = 0) := fun t ht =>
    ⟨fun h => by
      by_contra hz
      exact not_receiverBounded_oscWeight_one ht hz h,
    receiverBounded_oscWeight_one_of_zero ht⟩
  rcases lt_or_gt_of_ne ht₀ with hneg | hpos
  · rw [← oscWeight_neg 1 t₀, key (-t₀) (by linarith), riemannZeta_half_add_neg_eq_zero_iff]
  · exact key t₀ hpos

/-- **The phase diagram of the oscillating prime patterns.** For `a ∈ [−1, 1]` and `t₀ ∈ ℝ`, the
half-damped weight `f_{a,t₀}(d) d^{-1/2}`, `f(p) = a cos(t₀ log p)`, is paid exactly when `t₀ = 0` and
`a < 1/2`, or `t₀ ≠ 0` and either `a < 1` or `ζ(1/2 + it₀) = 0`. -/
theorem receiverBounded_oscWeight_iff {a t₀ : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1) :
    ReceiverBounded (oscWeight a t₀) ↔
      (t₀ = 0 ∧ a < 1 / 2) ∨ (t₀ ≠ 0 ∧ (a < 1 ∨ riemannZeta (1 / 2 + t₀ * I) = 0)) := by
  by_cases ht : t₀ = 0
  · subst ht
    rw [oscWeight_zero, receiverBounded_constantSign_iff_full ha ha1]
    constructor
    · intro h; exact Or.inl ⟨rfl, h⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact h
      · exact absurd rfl h
  · rcases ha1.lt_or_eq with hlt | heq
    · exact ⟨fun _ => Or.inr ⟨ht, Or.inl hlt⟩,
        fun _ => receiverBounded_oscWeight_of_lt_one ha hlt ht⟩
    · subst heq
      rw [receiverBounded_oscWeight_one_iff ht]
      constructor
      · intro h; exact Or.inr ⟨ht, Or.inr h⟩
      · rintro (⟨h, _⟩ | ⟨_, h | h⟩)
        · exact absurd h ht
        · exact absurd h (lt_irrefl 1)
        · exact h

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
