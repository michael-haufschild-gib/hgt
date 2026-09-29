import GaloisForLFunctions.HTGeometry.HamburgerCriticalLine
import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay

/-!
# Hamburger's method with a defect

Tools for running Hamburger's odd theorem when the completed Dirichlet series is known only on
a line right of the critical line, and its reflection carries an extra term (a defect).

* `inverse_mellin_shift`: the theta series as an inverse Mellin integral over `Re s = 2σ`, for any
  `2σ ≤ 3/2` with the remainder holomorphic on `2σ ≤ Re s ≤ 3/2`.
* `theta_add_dual_eq_of_rightLine`: with `G = E + β Γ_ℝ(· - 1)` known on `Re s = 3/4`,
  `θ(x) + x^{-1/2} θ(1/x) = β(1 + x^{-1/2})
    + (1/2π)[∫ x^{-(3/8+it)} G(3/4 + 2it) dt + ∫ x^{-(1/8+it)} G(3/4 - 2it) dt]`.
  The polar terms are the Mellin transforms of `x^{-1/2}(e^{-πx} - 1)` and `e^{-π/x} - 1` on
  `Re s = 3/4` and `Re s = 1/4`.
* `gamma_thin_strip_inverse_mellin`: for `1/4 < Re ρ < 3/4`, the inverse Mellin integrals of
  `Γ(w - ρ/2)` over `Re w = 3/8` and `Re w = 1/8` differ by `x^{-ρ/2}`.  This computes the jump of a
  simple pole on the critical line without residue calculus: `Γ` is the Mellin transform of `e^{-y}`
  right of `0` and of `e^{-y} - 1` on `(-1, 0)`.
* `hamburgerSeries_eq_of_coeffTheta_relation_defect`: the Laplace step for a theta relation
  `θ_a(x) = ε x^{-1/2} θ_b(1/x) + α + β x^{-1/2} + K(x)`, with the defect's Laplace transform
  continued holomorphically to `Re t > 0`.
* `coeff_eq_of_hamburgerSeries_periodic_re_pos_of_defect`: Hamburger's residue comparison is
  unchanged by a perturbation `K` with `(t - i n₀) K(t) → 0` at every `i n₀`.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Inverse Mellin representation on a line right of the critical line.**  If
`M θ(s/2) = E(s) + β Γ_ℝ(s - 1)` on `Re s = 3/2`, with `E` continuous on `2σ ≤ Re s ≤ 3/2`,
holomorphic inside and `O(1/(1 + t²))`, then for `y > 0`
`θ(y) - β y^{-1/2} e^{-πy} = (1/2π) ∫ y^{-(σ+it)} E(2σ + 2it) dt`. -/
theorem inverse_mellin_shift {θ : ℝ → ℂ} {E : ℂ → ℂ} {β : ℂ} {C σ : ℝ}
    (hσ : σ ≤ 3 / 4)
    (hθc : ContinuousOn θ (Ioi 0)) (hθm : MellinConvergent θ (3 / 4))
    (hEc : ContinuousOn E (verticalStrip (2 * σ) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 2 * σ < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (2 * σ) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 → mellin θ (s / 2) = E s + β * Complex.Gammaℝ (s - 1))
    {y : ℝ} (hy : 0 < y) :
    θ y - β * ((y : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi y) =
      (1 / (2 * Real.pi)) • ∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * I)) *
        E (2 * ((σ : ℂ) + t * I)) := by
  set φ : ℝ → ℂ := fun u => θ u - ((0 : ℂ) * expNegPi u +
    β * ((u : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi u)) with hφ
  have hφ_eq : φ y = θ y - β * ((y : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi y) := by
    simp [hφ]
  have hdata : ∀ t : ℝ, HasMellin φ (((3 / 4 : ℝ) : ℂ) + t * I)
      (E (2 * (((3 / 4 : ℝ) : ℂ) + t * I))) := by
    intro t
    set w : ℂ := ((3 / 4 : ℝ) : ℂ) + t * I with hw
    have hs : (2 * w).re = 3 / 2 := by simp [hw]; norm_num
    have h2w : 2 * w / 2 = w := by ring
    have hpol := hasMellin_polarRight 0 β (s := 2 * w) (by rw [hs]; norm_num)
    rw [h2w] at hpol
    have hθ : MellinConvergent θ w := MellinConvergent.of_re_eq hθm (by simp [hw])
    have hsub := hasMellin_sub hθ hpol.1
    refine ⟨hsub.1, ?_⟩
    rw [hsub.2, hpol.2]
    have := hR (2 * w) hs
    rw [h2w] at this
    rw [this]
    ring
  have hcont : ContinuousAt φ y := by
    have h1 : ContinuousAt θ y := hθc.continuousAt (Ioi_mem_nhds hy)
    have h2 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ (-(1 / 2 : ℂ))) y :=
      continuousAt_ofReal_cpow_const _ _ (Or.inr hy.ne')
    exact h1.sub ((continuousAt_const.mul continuous_expNegPi.continuousAt).add
      (continuousAt_const.mul (h2.mul continuous_expNegPi.continuousAt)))
  have hvert : VerticalIntegrable (mellin φ) (3 / 4 : ℝ) := by
    have h := integrable_cpow_mul_comp_line hEc hdecay (σ := 3 / 4) (by linarith) (by norm_num)
      (x := 1) one_pos
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [ofReal_one, one_cpow, one_mul]
    exact ((hdata t).2).symm
  have hconv : MellinConvergent φ ((3 / 4 : ℝ) : ℂ) := by simpa using (hdata 0).1
  have hinv := mellinInv_mellin_eq (3 / 4 : ℝ) φ hy hconv hvert hcont
  set G : ℂ → ℂ := fun w => (y : ℂ) ^ (-w) * E (2 * w) with hG
  have hI : mellinInv (3 / 4 : ℝ) (mellin φ) y =
      (1 / (2 * Real.pi)) • ∫ t : ℝ, G (((3 / 4 : ℝ) : ℂ) + t * I) := by
    unfold mellinInv
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hG, smul_eq_mul]
    rw [(hdata t).2]
  have hmaps : ∀ w ∈ verticalStrip σ (3 / 4), 2 * w ∈ verticalStrip (2 * σ) (3 / 2) := by
    intro w hw
    rw [mem_verticalStrip] at hw ⊢
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    constructor <;> linarith [hw.1, hw.2]
  have hGc : ContinuousOn G (verticalStrip σ (3 / 4)) := by
    refine ContinuousOn.mul ?_ ?_
    · exact (Continuous.const_cpow continuous_neg
        (Or.inl (by exact_mod_cast hy.ne'))).continuousOn
    · exact hEc.comp (continuous_const.mul continuous_id).continuousOn hmaps
  have hGd : DifferentiableOn ℂ G {z : ℂ | σ < z.re ∧ z.re < 3 / 4} := by
    refine DifferentiableOn.mul ?_ ?_
    · intro w _
      exact (differentiableAt_id.neg.const_cpow
        (Or.inl (by exact_mod_cast hy.ne'))).differentiableWithinAt
    · refine hEd.comp (differentiable_id.const_mul (2 : ℂ)).differentiableOn fun w hw => ?_
      simp only [Set.mem_setOf_eq] at hw ⊢
      simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
      constructor <;> linarith [hw.1, hw.2]
  have hshift : (∫ t : ℝ, G (((3 / 4 : ℝ) : ℂ) + t * I)) =
      ∫ t : ℝ, G ((σ : ℂ) + t * I) := by
    refine integral_vertical_line_eq_of_horizontal_tendsto_of_continuousOn hσ hGc hGd
      (integrable_cpow_mul_comp_line hEc hdecay le_rfl (by linarith) hy)
      (integrable_cpow_mul_comp_line hEc hdecay (by linarith) (by norm_num) hy) ?_ ?_
    · exact tendsto_integral_horizontal_cpow_mul_comp hdecay hσ le_rfl
        (by norm_num) hy (h := fun T => -T) (fun T => by ring)
    · exact tendsto_integral_horizontal_cpow_mul_comp hdecay hσ le_rfl
        (by norm_num) hy (h := fun T => T) (fun T => rfl)
  rw [← hφ_eq, ← hinv, hI, hshift]

/-- `(1 + y²) y^N e^{-πy/4}` is bounded on `y ≥ 0`. -/
theorem exists_bound_one_add_sq_mul_pow_mul_exp_neg (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 ≤ y →
      (1 + y ^ 2) * (y ^ N * Real.exp (-(Real.pi * y / 4))) ≤ K := by
  have hpi := Real.pi_pos
  set a : ℝ := Real.pi / 8 with ha
  have ha0 : 0 < a := by positivity
  refine ⟨(N + 2).factorial * a⁻¹ ^ (N + 2) + N.factorial * a⁻¹ ^ N, by positivity,
    fun y hy => ?_⟩
  have hkey : ∀ m : ℕ, y ^ m * Real.exp (-(Real.pi * y / 4)) ≤ m.factorial * a⁻¹ ^ m := by
    intro m
    have hx : 0 ≤ a * y := by positivity
    have h := Real.pow_div_factorial_le_exp _ hx m
    rw [div_le_iff₀ (by positivity)] at h
    have hle : Real.exp (-(Real.pi * y / 4)) ≤ Real.exp (-(a * y)) :=
      Real.exp_le_exp.mpr (by rw [ha]; nlinarith)
    have hmul : (a * y) ^ m * Real.exp (-(a * y)) ≤ m.factorial := by
      calc (a * y) ^ m * Real.exp (-(a * y))
          ≤ Real.exp (a * y) * m.factorial * Real.exp (-(a * y)) := by gcongr
        _ = m.factorial := by
            rw [mul_comm (Real.exp (a * y)), mul_assoc, ← Real.exp_add]; simp
    have hpow : y ^ m = a⁻¹ ^ m * (a * y) ^ m := by
      rw [mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ha0.ne', one_pow, one_mul]
    calc y ^ m * Real.exp (-(Real.pi * y / 4)) ≤ y ^ m * Real.exp (-(a * y)) := by gcongr
      _ = a⁻¹ ^ m * ((a * y) ^ m * Real.exp (-(a * y))) := by rw [hpow]; ring
      _ ≤ a⁻¹ ^ m * m.factorial := by gcongr
      _ = m.factorial * a⁻¹ ^ m := by ring
  have h2 := hkey (N + 2)
  have h0 := hkey N
  calc (1 + y ^ 2) * (y ^ N * Real.exp (-(Real.pi * y / 4)))
      = y ^ N * Real.exp (-(Real.pi * y / 4)) + y ^ (N + 2) * Real.exp (-(Real.pi * y / 4)) := by
        ring
    _ ≤ N.factorial * a⁻¹ ^ N + (N + 2).factorial * a⁻¹ ^ (N + 2) := add_le_add h0 h2
    _ = _ := by ring

/-- `Γ_ℝ` decays like `1/(1 + t²)` along a vertical line `Re s = a` avoiding its poles
`0, -2, -4, …`. -/
theorem exists_decay_Gammaℝ_vertical_line {a : ℝ} (ha : ∀ k : ℕ, a ≠ -(2 * k)) :
    ∃ C : ℝ, ∀ t : ℝ, ‖Complex.Gammaℝ ((a : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨Cg, N, hCg, hg⟩ := exists_sharp_bound_norm_Gamma_strip (a / 2) (a / 2)
  obtain ⟨K, hK0, hK⟩ := exists_bound_one_add_sq_mul_pow_mul_exp_neg N
  have hpi := Real.pi_pos
  have hdiffΓ : ∀ t : ℝ, DifferentiableAt ℂ Complex.Gamma (((a : ℂ) + t * I) / 2) := by
    intro t
    apply Complex.differentiableAt_Gamma
    intro m hm
    have hre := congrArg Complex.re hm
    have him := congrArg Complex.im hm
    simp at hre him
    subst him
    exact ha m (by linarith)
  have hcont : Continuous fun t : ℝ => Complex.Gammaℝ ((a : ℂ) + t * I) := by
    rw [continuous_iff_continuousAt]
    intro t
    have h1 : ContinuousAt (fun t : ℝ => (Real.pi : ℂ) ^ (-((a : ℂ) + t * I) / 2)) t :=
      (Continuous.const_cpow (by fun_prop)
        (Or.inl (by exact_mod_cast Real.pi_ne_zero))).continuousAt
    have h2 : ContinuousAt (fun t : ℝ => Complex.Gamma (((a : ℂ) + t * I) / 2)) t :=
      (hdiffΓ t).continuousAt.comp (f := fun t : ℝ => ((a : ℂ) + t * I) / 2) (by fun_prop)
    have e : (fun t : ℝ => Complex.Gammaℝ ((a : ℂ) + t * I)) = fun t : ℝ =>
        (Real.pi : ℂ) ^ (-((a : ℂ) + t * I) / 2) * Complex.Gamma (((a : ℂ) + t * I) / 2) :=
      funext fun t => Complex.Gammaℝ_def _
    rw [e]
    exact h1.mul h2
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max (5 * max M 0) (Real.pi ^ (-a / 2) * Cg * K), fun t => ?_⟩
  have hden : 0 < 1 + t ^ 2 := by positivity
  by_cases ht : |t| ≤ 2
  · have hb := (hM t (by rw [mem_Icc]; exact abs_le.mp ht)).trans (le_max_left M 0)
    have hsq : t ^ 2 ≤ 4 := by nlinarith [sq_abs t, abs_nonneg t]
    calc ‖Complex.Gammaℝ ((a : ℂ) + t * I)‖ ≤ max M 0 := hb
      _ ≤ 5 * max M 0 / (1 + t ^ 2) := by
          rw [le_div_iff₀ hden]; nlinarith [le_max_right M 0]
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · push Not at ht
    have hre : (((a : ℂ) + t * I) / 2).re = a / 2 := by simp
    have him : (((a : ℂ) + t * I) / 2).im = t / 2 := by simp
    have hG := hg (((a : ℂ) + t * I) / 2) (by rw [hre]) (by rw [hre])
      (by rw [him, abs_div, abs_two]; linarith)
    rw [him, abs_div, abs_two] at hG
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    have hre2 : (-((a : ℂ) + t * I) / 2).re = -a / 2 := by simp
    rw [hre2]
    have hexp : Real.exp (-(Real.pi * (|t| / 2) / 2)) = Real.exp (-(Real.pi * |t| / 4)) := by
      congr 1; ring
    rw [hexp] at hG
    have hpow : (|t| / 2) ^ N ≤ |t| ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
    have hKt := hK |t| (abs_nonneg t)
    rw [sq_abs] at hKt
    have hPi : 0 ≤ Real.pi ^ (-a / 2) := by positivity
    calc Real.pi ^ (-a / 2) * ‖Complex.Gamma (((a : ℂ) + t * I) / 2)‖
        ≤ Real.pi ^ (-a / 2) * (Cg * |t| ^ N * Real.exp (-(Real.pi * |t| / 4))) := by
          gcongr
          exact hG.trans (by gcongr)
      _ = Real.pi ^ (-a / 2) * Cg * (|t| ^ N * Real.exp (-(Real.pi * |t| / 4))) := by ring
      _ ≤ Real.pi ^ (-a / 2) * Cg * (K / (1 + t ^ 2)) := by
          gcongr
          rw [le_div_iff₀ hden]; linarith
      _ = Real.pi ^ (-a / 2) * Cg * K / (1 + t ^ 2) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- The inverse-Mellin integrand `x^{-(σ+it)} Γ_ℝ(a + ict)` is integrable when the line
`Re s = a` avoids the poles of `Γ_ℝ` and `c ≠ 0`. -/
theorem integrable_cpow_mul_Gammaℝ_line {σ a c x : ℝ} (hx : 0 < x) (hc : c ≠ 0)
    (ha : ∀ k : ℕ, a ≠ -(2 * k)) :
    Integrable fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + t * I)) *
      Complex.Gammaℝ ((a : ℂ) + ((c * t : ℝ) : ℂ) * I) := by
  obtain ⟨C, hC⟩ := exists_decay_Gammaℝ_vertical_line ha
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0)
    simpa using this
  have hcont : Continuous fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + t * I)) *
      Complex.Gammaℝ ((a : ℂ) + ((c * t : ℝ) : ℂ) * I) := by
    refine Continuous.mul (Continuous.const_cpow (by fun_prop)
      (Or.inl (by exact_mod_cast hx.ne'))) ?_
    have hdiff : ∀ t : ℝ, DifferentiableAt ℂ Complex.Gamma
        (((a : ℂ) + ((c * t : ℝ) : ℂ) * I) / 2) := by
      intro t
      apply Complex.differentiableAt_Gamma
      intro m hm
      have hre := congrArg Complex.re hm
      have him := congrArg Complex.im hm
      simp at hre him
      rcases him with h | h
      · exact hc h
      · subst h; exact ha m (by linarith)
    have e : (fun t : ℝ => Complex.Gammaℝ ((a : ℂ) + ((c * t : ℝ) : ℂ) * I)) = fun t : ℝ =>
        (Real.pi : ℂ) ^ (-((a : ℂ) + ((c * t : ℝ) : ℂ) * I) / 2) *
          Complex.Gamma (((a : ℂ) + ((c * t : ℝ) : ℂ) * I) / 2) :=
      funext fun t => Complex.Gammaℝ_def _
    rw [e, continuous_iff_continuousAt]
    intro t
    exact ((Continuous.const_cpow (by fun_prop)
      (Or.inl (by exact_mod_cast Real.pi_ne_zero))).continuousAt).mul
      ((hdiff t).continuousAt.comp (f := fun t : ℝ => ((a : ℂ) + ((c * t : ℝ) : ℂ) * I) / 2)
        (by fun_prop))
  have hc2 : 0 < c ^ 2 := by positivity
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (x ^ (-σ) * (C * max 1 (c ^ 2)⁻¹)))
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (-((σ : ℂ) + t * I)).re = -σ := by simp
  rw [hre]
  have hb := hC (c * t)
  have hkey : 1 + t ^ 2 ≤ max 1 (c ^ 2)⁻¹ * (1 + (c * t) ^ 2) := by
    rcases le_total 1 (c ^ 2) with h1 | h1
    · have : (c ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
      rw [max_eq_left this]; nlinarith [sq_nonneg t]
    · have : 1 ≤ (c ^ 2)⁻¹ := one_le_inv₀ hc2 |>.mpr h1
      rw [max_eq_right this, mul_add, mul_one, mul_pow, ← mul_assoc, inv_mul_cancel₀ hc2.ne',
        one_mul]
      linarith
  have h3 : (1 + (c * t) ^ 2)⁻¹ ≤ max 1 (c ^ 2)⁻¹ * (1 + t ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith [hkey]
  have hC' : ‖Complex.Gammaℝ ((a : ℂ) + ((c * t : ℝ) : ℂ) * I)‖ ≤ C * (1 + (c * t) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]; exact hb
  calc x ^ (-σ) * ‖Complex.Gammaℝ ((a : ℂ) + ((c * t : ℝ) : ℂ) * I)‖
      ≤ x ^ (-σ) * (C * (max 1 (c ^ 2)⁻¹ * (1 + t ^ 2)⁻¹)) := by
        gcongr
        exact hC'.trans (mul_le_mul_of_nonneg_left h3 hC0)
    _ = x ^ (-σ) * (C * max 1 (c ^ 2)⁻¹) * (1 + t ^ 2)⁻¹ := by ring

/-- **Theta relation from a line right of the critical line.**  Suppose
`M θ(s/2) = E(s) + β Γ_ℝ(s - 1)` on `Re s = 3/2`, with `E` continuous on `3/4 ≤ Re s ≤ 3/2`,
holomorphic inside and `O(1/(1 + t²))`, and let `G = E + β Γ_ℝ(· - 1)` on `Re s = 3/4`.  Then
`θ(x) + x^{-1/2} θ(1/x) = β (1 + x^{-1/2}) + (1/2π) [∫ x^{-(3/8+it)} G(3/4 + 2it) dt
  + ∫ x^{-(1/8+it)} G(3/4 - 2it) dt]`.

Both `θ(x)` and `θ(1/x)` are inverse Mellin integrals over `Re s = 3/4`.  The polar parts
`β Γ_ℝ(s - 1)` and `β Γ_ℝ(-s)` are the Mellin transforms of `β x^{-1/2}(e^{-πx} - 1)` on
`Re s = 3/4` and of `β(e^{-π/x} - 1)` on `Re s = 1/4`. -/
theorem theta_add_dual_eq_of_rightLine {θ : ℝ → ℂ} {E G : ℂ → ℂ} {β : ℂ} {C : ℝ}
    (hθc : ContinuousOn θ (Ioi 0)) (hθm : MellinConvergent θ (3 / 4))
    (hEc : ContinuousOn E (verticalStrip (3 / 4) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 3 / 4 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (3 / 4) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 → mellin θ (s / 2) = E s + β * Complex.Gammaℝ (s - 1))
    (hG : ∀ s : ℂ, s.re = 3 / 4 → G s = E s + β * Complex.Gammaℝ (s - 1))
    {x : ℝ} (hx : 0 < x) :
    θ x + (x : ℂ) ^ (-(1 / 2 : ℂ)) * θ x⁻¹ =
      β * (1 + (x : ℂ) ^ (-(1 / 2 : ℂ))) + (1 / (2 * Real.pi)) •
        ((∫ t : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) *
            G (2 * (((3 / 8 : ℝ) : ℂ) + t * I))) +
          ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
            G (2 * (((3 / 8 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I))) := by
  have h38 : (2 : ℝ) * (3 / 8) = 3 / 4 := by norm_num
  have hEc' : ContinuousOn E (verticalStrip (2 * (3 / 8)) (3 / 2)) := by rwa [h38]
  have hEd' : DifferentiableOn ℂ E {s : ℂ | 2 * (3 / 8 : ℝ) < s.re ∧ s.re < 3 / 2} := by
    rwa [h38]
  have hdecay' : ∀ s ∈ verticalStrip (2 * (3 / 8 : ℝ)) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2) := by
    rwa [h38]
  have hI1 := inverse_mellin_shift (σ := 3 / 8) (by norm_num) hθc hθm hEc' hEd' hdecay' hR hx
  have hI2 := inverse_mellin_shift (σ := 3 / 8) (by norm_num) hθc hθm hEc' hEd' hdecay' hR
    (inv_pos.mpr hx)
  rw [Complex.real_smul] at hI1 hI2
  -- integrability of the `E`-integrands
  have hint1 : Integrable fun t : ℝ => (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) *
      E (2 * (((3 / 8 : ℝ) : ℂ) + t * I)) :=
    integrable_cpow_mul_comp_line hEc hdecay (by norm_num) (by norm_num) hx
  have hpt : ∀ t : ℝ, (x : ℂ) ^ (-(1 / 2 : ℂ)) *
      (((x⁻¹ : ℝ) : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) *
        E (2 * (((3 / 8 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I))) =
      (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
        E (2 * (((3 / 8 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) := by
    intro t
    rw [ofReal_inv_cpow_eq hx, ← mul_assoc, ofReal_cpow_mul_ofReal_cpow hx]
    congr 2
    push_cast; ring
  have hint2 : Integrable fun t : ℝ => (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
      E (2 * (((3 / 8 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) := by
    have h := (integrable_cpow_mul_comp_line hEc hdecay (σ := 3 / 8) (by norm_num)
      (by norm_num) (inv_pos.mpr hx)).comp_neg
    exact ((h.const_mul ((x : ℂ) ^ (-(1 / 2 : ℂ))))).congr
      (Eventually.of_forall fun t => hpt t)
  have hreflect : (x : ℂ) ^ (-(1 / 2 : ℂ)) * ∫ t : ℝ,
      ((x⁻¹ : ℝ) : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) * E (2 * (((3 / 8 : ℝ) : ℂ) + t * I)) =
      ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
        E (2 * (((3 / 8 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) := by
    rw [← integral_const_mul, ← integral_neg_eq_self]
    exact integral_congr_ae (Eventually.of_forall fun t => hpt t)
  have hhalf : (x : ℂ) ^ (-(1 / 2 : ℂ)) * ((x⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
    rw [ofReal_inv_cpow_eq hx, ofReal_cpow_mul_ofReal_cpow hx]
    norm_num
  -- the two Gamma integrals
  have hnp : ∀ k : ℕ, (-1 / 4 : ℝ) ≠ -(2 * k) := by
    intro k h
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num at h
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
  have hΓ1 := integrable_cpow_mul_Gammaℝ_line (σ := 3 / 8) (c := 2) hx (by norm_num) hnp
  have hΓ2 := integrable_cpow_mul_Gammaℝ_line (σ := 1 / 8) (c := -2) hx (by norm_num) hnp
  set f₁ : ℝ → ℂ := fun u => (u : ℂ) ^ (-(1 / 2 : ℂ)) * expNegSubOne (Real.pi * u) with hf₁
  set f₂ : ℝ → ℂ := fun u => expNegSubOne (Real.pi * u⁻¹) with hf₂
  have hM1 : ∀ t : ℝ, HasMellin f₁ (((3 / 8 : ℝ) : ℂ) + t * I)
      (Complex.Gammaℝ (((-1 / 4 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I)) := by
    intro t
    have hs : (2 * (((3 / 8 : ℝ) : ℂ) + t * I)).re = 3 / 4 := by simp; norm_num
    have h := hasMellin_halfPow_expNegSubOne_pi (s := 2 * (((3 / 8 : ℝ) : ℂ) + t * I))
      (by rw [hs]; norm_num) (by rw [hs]; norm_num)
    rw [show 2 * (((3 / 8 : ℝ) : ℂ) + t * I) / 2 = ((3 / 8 : ℝ) : ℂ) + t * I by ring] at h
    convert h using 2
    push_cast; ring
  have hM2 : ∀ t : ℝ, HasMellin f₂ (((1 / 8 : ℝ) : ℂ) + t * I)
      (Complex.Gammaℝ (((-1 / 4 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I)) := by
    intro t
    have hs : (2 * (((1 / 8 : ℝ) : ℂ) + t * I)).re = 1 / 4 := by simp; norm_num
    have h := hasMellin_expNegSubOne_pi_inv (s := 2 * (((1 / 8 : ℝ) : ℂ) + t * I))
      (by rw [hs]; norm_num) (by rw [hs]; norm_num)
    rw [show 2 * (((1 / 8 : ℝ) : ℂ) + t * I) / 2 = ((1 / 8 : ℝ) : ℂ) + t * I by ring] at h
    convert h using 2
    push_cast; ring
  have hinv1 : f₁ x = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) *
      Complex.Gammaℝ (((-1 / 4 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I) := by
    have hvert : VerticalIntegrable (mellin f₁) (3 / 8 : ℝ) := by
      have h := integrable_cpow_mul_Gammaℝ_line (σ := 3 / 8) (c := 2) one_pos (by norm_num) hnp
      refine h.congr (Eventually.of_forall fun t => ?_)
      simp only [ofReal_one, one_cpow, one_mul]
      exact ((hM1 t).2).symm
    have hconv : MellinConvergent f₁ ((3 / 8 : ℝ) : ℂ) := by simpa using (hM1 0).1
    have hcont : ContinuousAt f₁ x :=
      (continuousAt_ofReal_cpow_const _ _ (Or.inr hx.ne')).mul
        (continuous_expNegSubOne.comp (continuous_const.mul continuous_id)).continuousAt
    rw [← mellinInv_mellin_eq (3 / 8 : ℝ) f₁ hx hconv hvert hcont]
    unfold mellinInv
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_eq_mul]
    rw [(hM1 t).2]
  have hinv2 : f₂ x = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
      Complex.Gammaℝ (((-1 / 4 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I) := by
    have hvert : VerticalIntegrable (mellin f₂) (1 / 8 : ℝ) := by
      have h := integrable_cpow_mul_Gammaℝ_line (σ := 1 / 8) (c := -2) one_pos (by norm_num) hnp
      refine h.congr (Eventually.of_forall fun t => ?_)
      simp only [ofReal_one, one_cpow, one_mul]
      exact ((hM2 t).2).symm
    have hconv : MellinConvergent f₂ ((1 / 8 : ℝ) : ℂ) := by simpa using (hM2 0).1
    have hcont : ContinuousAt f₂ x :=
      continuous_expNegSubOne.continuousAt.comp
        (continuousAt_const.mul (continuousAt_inv₀ hx.ne'))
    rw [← mellinInv_mellin_eq (1 / 8 : ℝ) f₂ hx hconv hvert hcont]
    unfold mellinInv
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_eq_mul]
    rw [(hM2 t).2]
  -- rewrite `G` through `E` and the Gamma terms
  have hGline1 : ∀ t : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) *
      G (2 * (((3 / 8 : ℝ) : ℂ) + t * I)) =
      (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) * E (2 * (((3 / 8 : ℝ) : ℂ) + t * I)) +
      β * ((x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) *
        Complex.Gammaℝ (((-1 / 4 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I)) := by
    intro t
    rw [hG _ (by simp; norm_num)]
    have : 2 * (((3 / 8 : ℝ) : ℂ) + t * I) - 1 = ((-1 / 4 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [this]; ring
  have hGline2 : ∀ t : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
      G (2 * (((3 / 8 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) =
      (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
        E (2 * (((3 / 8 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) +
      β * ((x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
        Complex.Gammaℝ (((-1 / 4 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I)) := by
    intro t
    rw [hG _ (by simp; norm_num)]
    have : 2 * (((3 / 8 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) - 1 =
        ((-1 / 4 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I := by push_cast; ring
    rw [this]; ring
  have hsplit1 : (∫ t : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) *
      G (2 * (((3 / 8 : ℝ) : ℂ) + t * I))) =
      (∫ t : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) * E (2 * (((3 / 8 : ℝ) : ℂ) + t * I))) +
      β * ∫ t : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) *
        Complex.Gammaℝ (((-1 / 4 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I) := by
    have h := integral_add hint1 (hΓ1.const_mul β)
    rw [integral_const_mul] at h
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall hGline1)
  have hsplit2 : (∫ t : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
      G (2 * (((3 / 8 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I))) =
      (∫ t : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
        E (2 * (((3 / 8 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I))) +
      β * ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
        Complex.Gammaℝ (((-1 / 4 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I) := by
    have h := integral_add hint2 (hΓ2.const_mul β)
    rw [integral_const_mul] at h
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall hGline2)
  rw [hsplit1, hsplit2]
  rw [Complex.real_smul] at hinv1 hinv2 ⊢
  have hf₁x : f₁ x = (x : ℂ) ^ (-(1 / 2 : ℂ)) * (expNegPi x - 1) := by
    simp only [hf₁, expNegSubOne_pi_mul]
  have hf₂x : f₂ x = expNegPi x⁻¹ - 1 := by
    simp only [hf₂, expNegSubOne_pi_mul]
  rw [hf₁x] at hinv1
  rw [hf₂x] at hinv2
  have e1 : θ x = β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi x) +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) *
        E (2 * (((3 / 8 : ℝ) : ℂ) + t * I)) := by
    linear_combination hI1
  have e2 : (x : ℂ) ^ (-(1 / 2 : ℂ)) * θ x⁻¹ = β * expNegPi x⁻¹ +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
        E (2 * (((3 / 8 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) := by
    rw [← hreflect]
    linear_combination (x : ℂ) ^ (-(1 / 2 : ℂ)) * hI2 + β * expNegPi x⁻¹ * hhalf
  rw [e1, e2]
  linear_combination β * hinv1 + β * hinv2

/-- **Hamburger's periodicity step with a vanishing perturbation.**  If
`L(t + i) − L(t) = c/(t + i) − c/t + K(t)` for `Re t > 0`, where `(t − i n₀) K(t) → 0` as `t → i n₀`
from the right half-plane for every `n₀ ≥ 0`, then every coefficient equals `−2πc`. -/
theorem coeff_eq_of_hamburgerSeries_periodic_re_pos_of_defect {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) (c : ℂ) (K : ℂ → ℂ)
    (hper : ∀ t : ℂ, 0 < t.re →
      hamburgerSeries a (t + I) - hamburgerSeries a t = c / (t + I) - c / t + K t)
    (hK : ∀ n₀ : ℕ, Tendsto (fun t => (t - (n₀ : ℂ) * I) * K t)
      (𝓝[{t : ℂ | 0 < t.re}] ((n₀ : ℂ) * I)) (𝓝 0))
    (n : ℕ) :
    a (n + 1) = -(2 * Real.pi * c) := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hev : ∀ y : ℝ, ∀ᶠ t in 𝓝[{t : ℂ | 0 < t.re}] ((y : ℂ) * I),
      hamburgerSeries a (t + I) - hamburgerSeries a t = c / (t + I) - c / t + K t := by
    intro y
    filter_upwards [self_mem_nhdsWithin] with t ht using hper t ht
  induction n with
  | zero =>
    haveI := nhdsWithin_re_pos_neBot 0
    have hle := nhdsWithin_re_pos_le_punctured 0
    simp only [ofReal_zero, zero_mul] at hle this
    have h1 := (tendsto_mul_hamburgerSeries_add_I ha).mono_left hle
    have h2 : Tendsto (fun t => t * hamburgerSeries a t) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ)) (𝓝 0) := by
      have hz : Tendsto (fun t : ℂ => t) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hL : Tendsto (hamburgerSeries a) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ)) (𝓝 0) :=
        (tendsto_hamburgerSeries_zero ha).mono_left nhdsWithin_le_nhds
      simpa using hz.mul hL
    have h3 : Tendsto (fun t => t * (c / (t + I) - c / t)) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ))
        (𝓝 (-c)) := by
      have hc : Tendsto (fun t : ℂ => t * (c / (t + I)) - c) (𝓝 (0 : ℂ))
          (𝓝 (0 * (c / (0 + I)) - c)) := by
        have hI : (0 : ℂ) + I ≠ 0 := by simp
        exact ((continuous_id.tendsto 0).mul ((continuous_const.tendsto 0).div
          ((continuous_id.add continuous_const).tendsto 0) hI)).sub tendsto_const_nhds
      simp only [zero_mul, zero_sub] at hc
      refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by
        rintro rfl
        simp at ht
      field_simp
    have hK0 : Tendsto (fun t => t * K t) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ)) (𝓝 0) := by
      have := hK 0
      simpa using this
    have h3' := h3.add hK0
    rw [add_zero] at h3'
    have h4 := h1.sub h2
    rw [sub_zero] at h4
    have h5 : Tendsto (fun t => t * hamburgerSeries a (t + I) - t * hamburgerSeries a t)
        (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ)) (𝓝 (-c)) := by
      have h0 := hev 0
      simp only [ofReal_zero, zero_mul] at h0
      refine h3'.congr' ?_
      filter_upwards [h0] with t ht
      rw [← mul_sub, ht]
      ring
    have huniq := tendsto_nhds_unique h4 h5
    rw [div_eq_iff hπ] at huniq
    rw [huniq]
    ring
  | succ n ih =>
    rw [← ih]
    set n₀ := n + 1 with hn₀def
    have hn₀ : 1 ≤ n₀ := by omega
    haveI := nhdsWithin_re_pos_neBot (n₀ : ℝ)
    have hle := nhdsWithin_re_pos_le_punctured (n₀ : ℝ)
    simp only [ofReal_natCast] at hle this
    have hA := (tendsto_sub_mul_hamburgerSeries ha hn₀).mono_left hle
    have hB := tendsto_sub_mul_hamburgerSeries ha (n₀ := n₀ + 1) (by omega)
    have hshift : Tendsto (fun t : ℂ => t + I) (𝓝[≠] ((n₀ : ℂ) * I))
        (𝓝[≠] (((n₀ + 1 : ℕ) : ℂ) * I)) := by
      have hc : Tendsto (fun t : ℂ => t + I) (𝓝 ((n₀ : ℂ) * I)) (𝓝 (((n₀ + 1 : ℕ) : ℂ) * I)) := by
        have := (continuous_id.add continuous_const).tendsto ((n₀ : ℂ) * I) (f := fun t : ℂ => t + I)
        convert this using 2
        push_cast; ring_nf
      refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
      intro h
      apply ht
      push_cast at h
      linear_combination h
    have hB'' : Tendsto (fun t => (t - (n₀ : ℂ) * I) * hamburgerSeries a (t + I))
        (𝓝[{t : ℂ | 0 < t.re}] ((n₀ : ℂ) * I)) (𝓝 (a (n₀ + 1) / (2 * Real.pi))) := by
      refine ((hB.comp hshift).mono_left hle).congr' (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp]
      congr 1
      push_cast; ring_nf
    have hn0 : (n₀ : ℂ) ≠ 0 := by exact_mod_cast (by omega : n₀ ≠ 0)
    have hR : Tendsto (fun t => (t - (n₀ : ℂ) * I) * (c / (t + I) - c / t))
        (𝓝[{t : ℂ | 0 < t.re}] ((n₀ : ℂ) * I)) (𝓝 0) := by
      have h1 : (n₀ : ℂ) * I + I ≠ 0 := by
        intro h
        have : ((n₀ : ℂ) + 1) * I = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h' | h'
        · have : ((n₀ + 1 : ℕ) : ℂ) = 0 := by push_cast; exact h'
          exact absurd (by exact_mod_cast this) (Nat.succ_ne_zero n₀)
        · exact I_ne_zero h'
      have h2 : (n₀ : ℂ) * I ≠ 0 := mul_ne_zero hn0 I_ne_zero
      have hc : ContinuousAt (fun t => (t - (n₀ : ℂ) * I) * (c / (t + I) - c / t))
          ((n₀ : ℂ) * I) := by
        refine ContinuousAt.mul (by fun_prop) (ContinuousAt.sub ?_ ?_)
        · exact continuousAt_const.div (by fun_prop) h1
        · exact continuousAt_const.div continuousAt_id h2
      have := hc.tendsto
      simp only [sub_self, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hR' := hR.add (hK n₀)
    rw [add_zero] at hR'
    have hdiff := hB''.sub hA
    have hdiff0 : Tendsto (fun t => (t - (n₀ : ℂ) * I) * hamburgerSeries a (t + I) -
        (t - (n₀ : ℂ) * I) * hamburgerSeries a t) (𝓝[{t : ℂ | 0 < t.re}] ((n₀ : ℂ) * I))
        (𝓝 0) := by
      have h0 := hev (n₀ : ℝ)
      simp only [ofReal_natCast] at h0
      refine hR'.congr' ?_
      filter_upwards [h0] with t ht
      rw [← mul_sub, ht]
      ring
    have huniq := tendsto_nhds_unique hdiff hdiff0
    rw [← sub_div] at huniq
    exact sub_eq_zero.mp ((div_eq_zero_iff.mp huniq).resolve_right hπ)

/-- **Laplace step with a defect, real form.**  If
`θ_a(x) = ε x^{-1/2} θ_b(1/x) + α + β x^{-1/2} + K(x)` for `x > 0`, then for real `t > 0`
`L_a(t) = ε Σ b_n e^{-2πnt} + α/(πt) + β + t ∫₀^∞ K(x) e^{-πt²x} dx`. -/
theorem hamburgerSeries_eq_of_coeffTheta_relation_defect_ofReal (a b : ℕ → ℂ)
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (hb : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {ε α β : ℂ} {K : ℝ → ℂ}
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + K x)
    {t : ℝ} (ht : 0 < t)
    (hKint : IntegrableOn (fun x : ℝ => K x * ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ))
      (Ioi 0)) :
    hamburgerSeries a t =
      ε * ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) +
        α / (Real.pi * t) + β +
          t * ∫ x in Ioi (0 : ℝ), K x * ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ) := by
  set e : ℝ → ℂ := fun x => ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ) with he_def
  have hB : 0 < Real.pi * t ^ 2 := by positivity
  have he_int : IntegrableOn e (Ioi 0) := (integrableOn_Ioi_exp_neg_mul hB).ofReal
  have hhe_eq : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x =
      ((x ^ ((1 / 2 : ℝ) - 1) * Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [he_def, Complex.ofReal_mul, Complex.ofReal_cpow hx0.le]
    push_cast
    ring_nf
  have hhe_int : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) (Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => x ^ ((1 / 2 : ℝ) - 1) *
        Real.exp (-(Real.pi * t ^ 2) * x ^ (1 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl hB
    have h' : IntegrableOn (fun x : ℝ => ((x ^ ((1 / 2 : ℝ) - 1) *
        Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ)) (Ioi 0) := by
      have := Integrable.ofReal (𝕜 := ℂ) h
      simp only [Real.rpow_one, neg_mul] at this
      exact this
    exact IntegrableOn.congr_fun h' (fun x hx => (hhe_eq x hx).symm) measurableSet_Ioi
  have hD_int := integrableOn_dual_coeffTheta_mul_exp b hb ht
  have hI0 : ∫ x in Ioi (0 : ℝ), e x = ((1 / (Real.pi * t ^ 2) : ℝ) : ℂ) := by
    rw [he_def, integral_complex_ofReal, integral_Ioi_exp_neg_mul hB]
  have hIh : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x = ((1 / t : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hhe_eq, integral_complex_ofReal,
      integral_Ioi_rpow_neg_half_mul_exp_neg_mul_sq ht]
  have hpt : ∀ x ∈ Ioi (0 : ℝ), coeffTheta a x * e x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ * e x) +
        (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) + K x * e x := by
    intro x hx
    rw [htheta x hx]
    ring
  have hsplit : ∫ x in Ioi (0 : ℝ), coeffTheta a x * e x =
      ε * (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ * e x) +
        (α * ∫ x in Ioi (0 : ℝ), e x) +
          β * (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) +
            ∫ x in Ioi (0 : ℝ), K x * e x := by
    have h1 : ∫ x in Ioi (0 : ℝ), (ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ * e x) +
        (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) + K x * e x) =
        (∫ x in Ioi (0 : ℝ), (ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ * e x) +
          (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)))) + ∫ x in Ioi (0 : ℝ), K x * e x :=
      integral_add ((hD_int.const_mul ε).add ((he_int.const_mul α).add (hhe_int.const_mul β)))
        hKint
    have h1' : ∫ x in Ioi (0 : ℝ), (ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ * e x) +
        (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x))) =
        (∫ x in Ioi (0 : ℝ), ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹ * e x)) +
          ∫ x in Ioi (0 : ℝ), (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) :=
      integral_add (hD_int.const_mul ε) ((he_int.const_mul α).add (hhe_int.const_mul β))
    have h2 : ∫ x in Ioi (0 : ℝ), (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) =
        (∫ x in Ioi (0 : ℝ), α * e x) +
          ∫ x in Ioi (0 : ℝ), β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) :=
      integral_add (he_int.const_mul α) (hhe_int.const_mul β)
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, h1, h1', h2, integral_const_mul,
      integral_const_mul, integral_const_mul]
    ring
  have hL := (hasSum_integral_coeffTheta_mul_exp a ha ht).tsum_eq
  have hD := (hasSum_integral_dual_coeffTheta_mul_exp b hb ht).tsum_eq
  rw [hsplit, ← hD, hI0, hIh] at hL
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hham : hamburgerSeries a t = (t : ℂ) * ∑' n : ℕ,
      a (n + 1) / ((Real.pi * (((n : ℝ) + 1) ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    rw [hamburgerSeries, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  have hdual : ∑' n : ℕ, b (n + 1) *
      ((1 / t * Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t)) : ℝ) : ℂ) =
      (1 / (t : ℂ)) * ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  rw [hham, hL, hdual]
  simp only [he_def]
  push_cast
  field_simp

/-- **Laplace step with a defect.**  Under the defect theta relation, if `J` is holomorphic on
`Re t > 0` and equals `t ∫₀^∞ K(x) e^{-πt²x} dx` for real `t > 0`, then on `Re t > 0`
`L_a(t) = ε Σ b_n e^{-2πnt} + α/(πt) + β + J(t)`. -/
theorem hamburgerSeries_eq_of_coeffTheta_relation_defect (a b : ℕ → ℂ)
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (hb : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {ε α β : ℂ} {K : ℝ → ℂ} {J : ℂ → ℂ}
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + K x)
    (hKint : ∀ t : ℝ, 0 < t →
      IntegrableOn (fun x : ℝ => K x * ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)) (Ioi 0))
    (hJd : DifferentiableOn ℂ J {t : ℂ | 0 < t.re})
    (hJ : ∀ t : ℝ, 0 < t →
      J t = t * ∫ x in Ioi (0 : ℝ), K x * ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ))
    {t : ℂ} (ht : 0 < t.re) :
    hamburgerSeries a t =
      ε * ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) +
        α / (Real.pi * t) + β + J t := by
  set U : Set ℂ := {t : ℂ | 0 < t.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := summable_sq_of_forall_rpow ha
    simpa using this
  have hf : AnalyticOnNhd ℂ (hamburgerSeries a) U :=
    (differentiableOn_hamburgerSeries ha2).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (fun t : ℂ => ε * ∑' n : ℕ, b (n + 1) *
      cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) + α / (Real.pi * t) + β + J t) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    refine ((((differentiableOn_expDualSeries (summable_sq_of_forall_rpow hb)).const_mul ε).add
      ?_).add (differentiableOn_const _)).add hJd
    refine DifferentiableOn.div (differentiableOn_const _) (by fun_prop) fun t ht => ?_
    have ht' : 0 < t.re := ht
    refine mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) fun h => ?_
    rw [h, zero_re] at ht'
    exact lt_irrefl _ ht'
  have h1U : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), hamburgerSeries a z = ε * ∑' n : ℕ, b (n + 1) *
      cexp (-(2 * Real.pi * ((n : ℂ) + 1) * z)) + α / (Real.pi * z) + β + J z := by
    set u : ℕ → ℂ := fun k => ((1 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ) with hu
    have hlim : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
        rw [add_zero] at h
        have h2 := (Complex.continuous_ofReal.tendsto 1).comp h
        rw [Complex.ofReal_one] at h2
        exact h2
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hu]
        intro h
        have h' : (1 + 1 / ((k : ℝ) + 1) : ℝ) = 1 := by exact_mod_cast h
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    refine hlim.frequently (Frequently.of_forall fun k => ?_)
    have hk : (0 : ℝ) < 1 + 1 / ((k : ℝ) + 1) := by positivity
    simp only [hu]
    rw [hJ _ hk]
    exact hamburgerSeries_eq_of_coeffTheta_relation_defect_ofReal a b ha hb htheta hk (hKint _ hk)
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 0).isPreconnected
    h1U hfreq ht

/-- `Γ` is integrable along every vertical line `Re z = a` avoiding its poles. -/
theorem integrable_Gamma_vertical_line {a b : ℝ} (ha : ∀ k : ℕ, a ≠ -(k : ℝ)) :
    Integrable fun t : ℝ => Complex.Gamma ((a : ℂ) + ((t - b : ℝ) : ℂ) * I) := by
  obtain ⟨Cg, N, hCg, hg⟩ := exists_sharp_bound_norm_Gamma_strip a a
  obtain ⟨K, hK0, hK⟩ := exists_bound_one_add_sq_mul_pow_mul_exp_neg N
  have hdiff : ∀ y : ℝ, DifferentiableAt ℂ Complex.Gamma ((a : ℂ) + (y : ℂ) * I) := by
    intro y
    apply Complex.differentiableAt_Gamma
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    exact ha m hre
  have hcont : Continuous fun y : ℝ => Complex.Gamma ((a : ℂ) + (y : ℂ) * I) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (hdiff y).continuousAt.comp (f := fun y : ℝ => (a : ℂ) + (y : ℂ) * I) (by fun_prop)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hpi := Real.pi_pos
  have hbound : ∀ y : ℝ, ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ ≤
      max (2 * max M 0) (Cg * K) * (1 + y ^ 2)⁻¹ := by
    intro y
    have hden : 0 < 1 + y ^ 2 := by positivity
    by_cases hy : |y| ≤ 1
    · have hb := (hM y (by rw [mem_Icc]; exact abs_le.mp hy)).trans (le_max_left M 0)
      have hsq : y ^ 2 ≤ 1 := by nlinarith [sq_abs y, abs_nonneg y]
      calc ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ ≤ max M 0 := hb
        _ ≤ 2 * max M 0 * (1 + y ^ 2)⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ hden]; nlinarith [le_max_right M 0]
        _ ≤ _ := by gcongr; exact le_max_left _ _
    · push Not at hy
      have hG := hg ((a : ℂ) + (y : ℂ) * I) (by simp) (by simp) (by simp; linarith)
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add] at hG
      have hexp : Real.exp (-(Real.pi * |y| / 2)) ≤ Real.exp (-(Real.pi * |y| / 4)) :=
        Real.exp_le_exp.mpr (by nlinarith [abs_nonneg y])
      have hKy := hK |y| (abs_nonneg y)
      rw [sq_abs] at hKy
      calc ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖
          ≤ Cg * |y| ^ N * Real.exp (-(Real.pi * |y| / 2)) := hG
        _ ≤ Cg * (|y| ^ N * Real.exp (-(Real.pi * |y| / 4))) := by
            rw [← mul_assoc]; gcongr
        _ ≤ Cg * (K * (1 + y ^ 2)⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ hCg
            rw [← div_eq_mul_inv, le_div_iff₀ hden]
            linarith [mul_comm (1 + y ^ 2) (|y| ^ N * Real.exp (-(Real.pi * |y| / 4)))]
        _ = Cg * K * (1 + y ^ 2)⁻¹ := by ring
        _ ≤ _ := by gcongr; exact le_max_right _ _
  have hint : Integrable fun y : ℝ => Complex.Gamma ((a : ℂ) + (y : ℂ) * I) :=
    Integrable.mono' ((integrable_inv_one_add_sq).const_mul _) hcont.aestronglyMeasurable
      (Eventually.of_forall hbound)
  exact hint.comp_sub_right b

/-- **The Γ thin-strip identity.**  For `1/4 < Re ρ < 3/4` and `x > 0`,
`(1/2π) [∫ x^{-(3/8+it)} Γ(3/8 + it - ρ/2) dt - ∫ x^{-(1/8+it)} Γ(1/8 + it - ρ/2) dt] = x^{-ρ/2}`.
The two integrals are the inverse Mellin transforms of `y^{-ρ/2} e^{-y}` and of
`y^{-ρ/2}(e^{-y} - 1)`: `Γ` is the Mellin transform of `e^{-y}` right of `0` and of `e^{-y} - 1`
on `(-1, 0)`. -/
theorem gamma_thin_strip_inverse_mellin {ρ : ℂ} (h1 : 1 / 4 < ρ.re) (h2 : ρ.re < 3 / 4)
    {x : ℝ} (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℝ) • ((∫ t : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) *
        Complex.Gamma (((3 / 8 : ℝ) : ℂ) + t * I - ρ / 2)) -
      ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
        Complex.Gamma (((1 / 8 : ℝ) : ℂ) + t * I - ρ / 2)) = (x : ℂ) ^ (-(ρ / 2)) := by
  set f : ℝ → ℂ := fun y => (y : ℂ) ^ (-(ρ / 2)) • ((Real.exp (-y) : ℝ) : ℂ) with hf
  set g : ℝ → ℂ := fun y => (y : ℂ) ^ (-(ρ / 2)) • expNegSubOne y with hg
  have hline : ∀ (σ : ℝ) (t : ℝ), ((σ : ℂ) + t * I - ρ / 2) =
      (((σ - ρ.re / 2 : ℝ)) : ℂ) + ((t - ρ.im / 2 : ℝ) : ℂ) * I := by
    intro σ t
    apply Complex.ext <;> simp
  have hMf : ∀ t : ℝ, HasMellin f (((3 / 8 : ℝ) : ℂ) + t * I)
      (Complex.Gamma (((3 / 8 : ℝ) : ℂ) + t * I - ρ / 2)) := by
    intro t
    have hre : 0 < (((3 / 8 : ℝ) : ℂ) + t * I + -(ρ / 2)).re := by simp; linarith
    refine ⟨MellinConvergent.cpow_smul.mpr ?_, ?_⟩
    · exact (Complex.GammaIntegral_convergent hre).congr_fun (fun y _ => by
        simp only [smul_eq_mul]; ring) measurableSet_Ioi
    · rw [mellin_cpow_smul, mellin_exp_neg hre, sub_eq_add_neg]
  have hMg : ∀ t : ℝ, HasMellin g (((1 / 8 : ℝ) : ℂ) + t * I)
      (Complex.Gamma (((1 / 8 : ℝ) : ℂ) + t * I - ρ / 2)) := by
    intro t
    have hre1 : -1 < (((1 / 8 : ℝ) : ℂ) + t * I + -(ρ / 2)).re := by simp; linarith
    have hre2 : (((1 / 8 : ℝ) : ℂ) + t * I + -(ρ / 2)).re < 0 := by simp; linarith
    refine ⟨MellinConvergent.cpow_smul.mpr (mellinConvergent_expNegSubOne hre1 hre2), ?_⟩
    rw [mellin_cpow_smul, mellin_expNegSubOne hre1 hre2, sub_eq_add_neg]
  have hpolesf : ∀ k : ℕ, (3 / 8 - ρ.re / 2 : ℝ) ≠ -(k : ℝ) := by
    intro k h
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith
  have hpolesg : ∀ k : ℕ, (1 / 8 - ρ.re / 2 : ℝ) ≠ -(k : ℝ) := by
    intro k h
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp at h; linarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
  -- integrability of the two inverse-Mellin integrands
  have hcpow_bound : ∀ (σ z : ℝ), 0 < z → ∀ t : ℝ,
      ‖(z : ℂ) ^ (-((σ : ℂ) + t * I))‖ ≤ z ^ (-σ) := by
    intro σ z hz t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hz]
    simp
  have hcpow_meas : ∀ (σ z : ℝ), 0 < z →
      AEStronglyMeasurable (fun t : ℝ => (z : ℂ) ^ (-((σ : ℂ) + t * I))) volume := by
    intro σ z hz
    exact (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hz.ne'))).aestronglyMeasurable
  have hΓf : Integrable fun t : ℝ => Complex.Gamma (((3 / 8 : ℝ) : ℂ) + t * I - ρ / 2) := by
    refine (integrable_Gamma_vertical_line (b := ρ.im / 2) hpolesf).congr
      (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [hline]
  have hΓg : Integrable fun t : ℝ => Complex.Gamma (((1 / 8 : ℝ) : ℂ) + t * I - ρ / 2) := by
    refine (integrable_Gamma_vertical_line (b := ρ.im / 2) hpolesg).congr
      (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [hline]
  have hintf : ∀ z : ℝ, 0 < z → Integrable fun t : ℝ =>
      (z : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) * Complex.Gamma (((3 / 8 : ℝ) : ℂ) + t * I - ρ / 2) :=
    fun z hz => hΓf.bdd_mul (hcpow_meas _ z hz) (Eventually.of_forall (hcpow_bound _ z hz))
  have hintg : ∀ z : ℝ, 0 < z → Integrable fun t : ℝ =>
      (z : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) * Complex.Gamma (((1 / 8 : ℝ) : ℂ) + t * I - ρ / 2) :=
    fun z hz => hΓg.bdd_mul (hcpow_meas _ z hz) (Eventually.of_forall (hcpow_bound _ z hz))
  -- Mellin inversion on the two lines
  have hinvf : f x = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + t * I)) *
      Complex.Gamma (((3 / 8 : ℝ) : ℂ) + t * I - ρ / 2) := by
    have hvert : VerticalIntegrable (mellin f) (3 / 8 : ℝ) := by
      refine (hintf 1 one_pos).congr (Eventually.of_forall fun t => ?_)
      simp only [ofReal_one, one_cpow, one_mul]
      exact ((hMf t).2).symm
    have hconv : MellinConvergent f ((3 / 8 : ℝ) : ℂ) := by simpa using (hMf 0).1
    have hcont : ContinuousAt f x :=
      (continuousAt_ofReal_cpow_const _ _ (Or.inr hx.ne')).smul
        (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousAt
    rw [← mellinInv_mellin_eq (3 / 8 : ℝ) f hx hconv hvert hcont]
    unfold mellinInv
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_eq_mul]
    rw [(hMf t).2]
  have hinvg : g x = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + t * I)) *
      Complex.Gamma (((1 / 8 : ℝ) : ℂ) + t * I - ρ / 2) := by
    have hvert : VerticalIntegrable (mellin g) (1 / 8 : ℝ) := by
      refine (hintg 1 one_pos).congr (Eventually.of_forall fun t => ?_)
      simp only [ofReal_one, one_cpow, one_mul]
      exact ((hMg t).2).symm
    have hconv : MellinConvergent g ((1 / 8 : ℝ) : ℂ) := by simpa using (hMg 0).1
    have hcont : ContinuousAt g x :=
      (continuousAt_ofReal_cpow_const _ _ (Or.inr hx.ne')).smul continuous_expNegSubOne.continuousAt
    rw [← mellinInv_mellin_eq (1 / 8 : ℝ) g hx hconv hvert hcont]
    unfold mellinInv
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_eq_mul]
    rw [(hMg t).2]
  rw [smul_sub, ← hinvf, ← hinvg]
  simp only [hf, hg, smul_eq_mul, expNegSubOne]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry

