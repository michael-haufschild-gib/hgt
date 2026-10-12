import GaloisForLFunctions.HTGeometry.LerchHurwitzDerivative
import Mathlib.NumberTheory.LSeries.HurwitzZeta

/-!
# The Euler–Maclaurin form of the Hurwitz zeta function, uniformly in the shift

For `a > 0` the second-order Euler–Maclaurin function

`ζ_EM(s, a) = a^{1−s}/(s − 1) + a^{−s}/2 − s(s + 1) ∫_0^∞ P₂(x)(x + a)^{−s−2} dx`

is holomorphic on `Re s > −½`, `s ≠ 1` (`differentiableAt_hurwitzZetaEM`).  For `0 < a ≤ 1` it
continues the tail of the Hurwitz series:

`ζ(s, a) = a^{−s} + ζ_EM(s, a + 1)`   (`hurwitzZeta_eq_rpow_add_hurwitzZetaEM`),

where `ζ(s, a)` is Mathlib's `hurwitzZeta`.  On the strip `−½ ≤ Re s ≤ 3/2` the tail is bounded
uniformly in the shift (`norm_hurwitzZetaEM_le`, valid on all of `Re s ≥ −½`):

`‖ζ_EM(s, b)‖ ≤ 2^{3/2}/|s − 1| + 2 + |s||s + 1|/4`   for `1 ≤ b ≤ 2`.

So the only non-uniform part of `ζ(s, a)` as `a → 0⁺` is the explicit term `a^{−s}`.
-/

open Filter Real MeasureTheory Set Complex
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The kernel integral -/

/-- `∫_0^∞ (x + a)^{−p} dx = a^{1−p}/(p − 1)` for `p > 1`. -/
theorem integral_Ioi_shift_rpow_neg {a p : ℝ} (ha : 0 < a) (hp : 1 < p) :
    ∫ x in Ioi (0 : ℝ), (x + a) ^ (-p) = a ^ (1 - p) / (p - 1) := by
  have hp0 : (0 : ℝ) < p - 1 := by linarith
  have hcont : ContinuousWithinAt (fun x : ℝ => -((x + a) ^ (1 - p) / (p - 1))) (Ici 0) 0 := by
    refine (ContinuousAt.neg (ContinuousAt.div ?_ continuousAt_const (by linarith))).continuousWithinAt
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (by simpa using ne_of_gt ha))).comp
      (by fun_prop)
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => -((x + a) ^ (1 - p) / (p - 1)))
      ((x + a) ^ (-p)) x := by
    intro x hx
    have hxa : (0 : ℝ) < x + a := by have : (0 : ℝ) < x := hx; linarith
    have hd := (hasDerivAt_shift_rpow (a := a) (q := 1 - p) hxa).div_const (p - 1)
    refine (hd.neg).congr_deriv ?_
    rw [show 1 - p - 1 = -p by ring]
    field_simp
    ring
  have hlim : Tendsto (fun x : ℝ => -((x + a) ^ (1 - p) / (p - 1))) atTop (𝓝 0) := by
    have hbase : Tendsto (fun x : ℝ => x + a) atTop atTop := tendsto_atTop_add_const_right _ a tendsto_id
    have hr : Tendsto (fun t : ℝ => t ^ (-(p - 1))) atTop (𝓝 0) := tendsto_rpow_neg_atTop hp0
    have := ((hr.comp hbase).div_const (p - 1)).neg
    rw [zero_div, neg_zero] at this
    refine this.congr fun x => ?_
    simp only [Function.comp_apply]
    congr 2
    ring_nf
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv (fun x hx => by
    have : (0 : ℝ) < x + a := by have : (0 : ℝ) < x := hx; linarith
    positivity) hlim]
  simp only [zero_add, zero_sub, neg_neg]

/-- `‖∫_0^∞ P₂(x)(x + a)^{−s−2} dx‖ ≤ ¼ a^{−Re s − 1}` for `Re s ≥ −½`. -/
theorem norm_emKernel_le {a : ℝ} (ha : 0 < a) {s : ℂ} (h1 : -(1 / 2 : ℝ) ≤ s.re) :
    ‖emKernel a s‖ ≤ 1 / 4 * a ^ (-s.re - 1) := by
  unfold emKernel
  have hdom : IntegrableOn
      (fun x : ℝ => (1 / 8) * a ^ (-s.re - 1 / 2) * (x + a) ^ (-(3 / 2 : ℝ))) (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_shift_rpow_neg ha (by norm_num)).const_mul _
  calc ‖∫ x in Ioi (0 : ℝ), ((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-s - 2)‖
      ≤ ∫ x in Ioi (0 : ℝ), (1 / 8) * a ^ (-s.re - 1 / 2) * (x + a) ^ (-(3 / 2 : ℝ)) := by
        refine norm_integral_le_of_norm_le hdom ?_
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
        exact norm_emKernel_integrand_le' ha h1 hx
    _ = (1 / 8) * a ^ (-s.re - 1 / 2) * (a ^ (1 - 3 / 2 : ℝ) / (3 / 2 - 1)) := by
        rw [integral_const_mul, integral_Ioi_shift_rpow_neg ha (by norm_num)]
    _ = 1 / 4 * a ^ (-s.re - 1) := by
        rw [show (1 - 3 / 2 : ℝ) = -(1 / 2) by norm_num, mul_assoc,
          show a ^ (-s.re - 1 / 2) * (a ^ (-(1 / 2) : ℝ) / (3 / 2 - 1)) =
            2 * (a ^ (-s.re - 1 / 2) * a ^ (-(1 / 2) : ℝ)) by ring, ← Real.rpow_add ha]
        ring_nf

/-- Holomorphy of the Euler–Maclaurin kernel on `Re s > −½`. -/
theorem differentiableAt_emKernel {a : ℝ} (ha : 0 < a) {s₀ : ℂ} (hs : -(1 / 2 : ℝ) < s₀.re) :
    DifferentiableAt ℂ (emKernel a) s₀ := by
  set ε : ℝ := (s₀.re + 1 / 2) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set σ₁ : ℝ := s₀.re - ε with hσ₁
  have hσ₁' : -(1 / 2 : ℝ) < σ₁ := by rw [hσ₁, hε]; linarith
  set M : ℝ := max 1 (a ^ (-(2 * ε))) with hM
  set F : ℂ → ℝ → ℂ := fun s x => ((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-s - 2)
    with hF
  set F' : ℂ → ℝ → ℂ := fun s x =>
    ((bernoulliHalfPer x : ℝ) : ℂ) * (((x + a : ℝ) : ℂ) ^ (-s - 2) * (-((Real.log (x + a) : ℝ) : ℂ)))
    with hF'
  -- the dominating function
  set bound : ℝ → ℝ := fun x => (1 / 8) * M * (|Real.log a| * (x + a) ^ (-(σ₁ + 2)) +
    4 * (x + a) ^ (-(σ₁ + 2 - 1 / 4))) with hbound
  have hpow_le : ∀ x : ℝ, 0 < x → ∀ s ∈ Metric.ball s₀ ε,
      ‖((x + a : ℝ) : ℂ) ^ (-s - 2)‖ ≤ M * (x + a) ^ (-(σ₁ + 2)) := by
    intro x hx s hs'
    have hxa : (0 : ℝ) < x + a := by linarith
    have hre : |s.re - s₀.re| < ε := by
      have := Metric.mem_ball.mp hs'
      rw [Complex.dist_eq] at this
      exact lt_of_le_of_lt (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _) this
    rw [norm_shiftCpow hxa]
    have hsplit : (x + a) ^ (-s.re - 2) = (x + a) ^ (-(σ₁ + 2)) * (x + a) ^ (σ₁ - s.re) := by
      rw [← Real.rpow_add hxa]; congr 1; ring
    rw [hsplit, mul_comm M]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hxa.le _)
    have hexp1 : σ₁ - s.re ≤ 0 := by rw [hσ₁]; linarith [(abs_lt.mp hre).1]
    have hexp2 : -(2 * ε) ≤ σ₁ - s.re := by rw [hσ₁]; linarith [(abs_lt.mp hre).2]
    rcases le_or_gt 1 (x + a) with hge | hlt
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hge hexp1).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      calc (x + a) ^ (σ₁ - s.re) ≤ (x + a) ^ (-(2 * ε)) :=
            Real.rpow_le_rpow_of_exponent_ge hxa hlt.le hexp2
        _ ≤ a ^ (-(2 * ε)) :=
            Real.rpow_le_rpow_of_nonpos ha (by linarith) (by linarith)
  have hlog_le : ∀ x : ℝ, 0 < x → |Real.log (x + a)| ≤ |Real.log a| + 4 * (x + a) ^ (1 / 4 : ℝ) := by
    intro x hx
    have hxa : (0 : ℝ) < x + a := by linarith
    rcases le_or_gt 1 (x + a) with hge | hlt
    · have hl := Real.log_le_rpow_div hxa.le (show (0 : ℝ) < 1 / 4 by norm_num)
      rw [abs_of_nonneg (Real.log_nonneg hge)]
      have : (x + a) ^ (1 / 4 : ℝ) / (1 / 4) = 4 * (x + a) ^ (1 / 4 : ℝ) := by ring
      rw [this] at hl
      linarith [abs_nonneg (Real.log a)]
    · have hneg : Real.log (x + a) < 0 := Real.log_neg hxa hlt
      rw [abs_of_neg hneg]
      have hmono : Real.log a ≤ Real.log (x + a) := Real.log_le_log ha (by linarith)
      have : -Real.log (x + a) ≤ |Real.log a| := by
        have := neg_abs_le (Real.log a)
        linarith
      linarith [Real.rpow_nonneg hxa.le (1 / 4 : ℝ)]
  have hbound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    have h1 := (integrableOn_Ioi_shift_rpow_neg ha (p := σ₁ + 2) (by linarith)).const_mul |Real.log a|
    have h2 := (integrableOn_Ioi_shift_rpow_neg ha (p := σ₁ + 2 - 1 / 4) (by linarith)).const_mul 4
    have h3 := (h1.add h2).const_mul ((1 / 8) * M)
    exact h3
  have hball : Metric.ball s₀ ε ∈ 𝓝 s₀ := Metric.ball_mem_nhds s₀ hε0
  have hmeas : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (F s) (volume.restrict (Ioi (0 : ℝ))) :=
    Eventually.of_forall fun s => aestronglyMeasurable_emKernel_integrand ha s
  have hint : Integrable (F s₀) (volume.restrict (Ioi (0 : ℝ))) :=
    integrableOn_emKernel_integrand' ha hs.le
  have hF'meas : AEStronglyMeasurable (F' s₀) (volume.restrict (Ioi (0 : ℝ))) := by
    have h1 := aestronglyMeasurable_emKernel_integrand ha s₀
    have h2 : AEStronglyMeasurable (fun x : ℝ => -((Real.log (x + a) : ℝ) : ℂ))
        (volume.restrict (Ioi (0 : ℝ))) :=
      (Complex.measurable_ofReal.comp (Real.measurable_log.comp
        (measurable_id.add_const a))).neg.aestronglyMeasurable
    refine (h1.mul h2).congr (Eventually.of_forall fun x => ?_)
    simp only [hF', Pi.mul_apply]
    ring
  have hbd : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ∀ s ∈ Metric.ball s₀ ε, ‖F' s x‖ ≤ bound x := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx s hs'
    have hx0 : (0 : ℝ) < x := hx
    have hxa : (0 : ℝ) < x + a := by linarith
    simp only [hF', hbound, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg]
    have hB := abs_bernoulliHalfPer_le x
    have hP := hpow_le x hx0 s hs'
    have hL := hlog_le x hx0
    have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
    have hsplit : (x + a) ^ (-(σ₁ + 2 - 1 / 4)) = (x + a) ^ (-(σ₁ + 2)) * (x + a) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hxa]; congr 1; ring
    rw [hsplit]
    calc |bernoulliHalfPer x| * (‖((x + a : ℝ) : ℂ) ^ (-s - 2)‖ * |Real.log (x + a)|)
        ≤ (1 / 8) * ((M * (x + a) ^ (-(σ₁ + 2))) * (|Real.log a| + 4 * (x + a) ^ (1 / 4 : ℝ))) := by
          refine mul_le_mul hB (mul_le_mul hP hL (abs_nonneg _) (by positivity)) (by positivity)
            (by norm_num)
      _ = (1 / 8) * M * (|Real.log a| * (x + a) ^ (-(σ₁ + 2)) +
            4 * ((x + a) ^ (-(σ₁ + 2)) * (x + a) ^ (1 / 4 : ℝ))) := by ring
  have hdiff : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ∀ s ∈ Metric.ball s₀ ε,
      HasDerivAt (fun s => F s x) (F' s x) s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx s _
    have hx0 : (0 : ℝ) < x := hx
    have hxa : (0 : ℝ) < x + a := by linarith
    have hne : ((x + a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxa.ne'
    have hlog : Complex.log ((x + a : ℝ) : ℂ) = ((Real.log (x + a) : ℝ) : ℂ) :=
      (Complex.ofReal_log hxa.le).symm
    have h1 : HasDerivAt (fun s : ℂ => -s - 2) (-1) s := by
      simpa using ((hasDerivAt_id s).neg).sub_const 2
    have h2 := h1.const_cpow (c := ((x + a : ℝ) : ℂ)) (Or.inl hne)
    have h3 := h2.const_mul ((bernoulliHalfPer x : ℝ) : ℂ)
    refine h3.congr_deriv ?_
    simp only [hF', hlog]
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hmeas hint hF'meas hbd
    hbound_int hdiff).2.differentiableAt

/-! ### The Euler–Maclaurin function -/

theorem differentiableAt_hurwitzZetaEM {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : -(1 / 2 : ℝ) < s.re)
    (hs1 : s ≠ 1) : DifferentiableAt ℂ (hurwitzZetaEM a) s := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hk := differentiableAt_emKernel ha hs
  unfold hurwitzZetaEM
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (a : ℂ) ^ (1 - s)) s :=
    ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow (Or.inl hane)
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (a : ℂ) ^ (-s)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hane)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  exact ((h1.div (differentiableAt_id.sub_const 1) hs1').add (h2.div_const 2)).sub
    ((differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul hk)

/-- **The uniform bound.**  For `1 ≤ b ≤ 2` and `Re s ≥ −½`,
`‖ζ_EM(s, b)‖ ≤ 2^{3/2}/|s − 1| + 2 + |s||s + 1|/4`. -/
theorem norm_hurwitzZetaEM_le {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) {s : ℂ}
    (h1 : -(1 / 2 : ℝ) ≤ s.re) :
    ‖hurwitzZetaEM b s‖ ≤ 2 ^ (3 / 2 : ℝ) / ‖s - 1‖ + 2 + ‖s‖ * ‖s + 1‖ / 4 := by
  have hb0 : (0 : ℝ) < b := by linarith
  unfold hurwitzZetaEM
  have hA : ‖((b : ℝ) : ℂ) ^ (1 - s)‖ ≤ 2 ^ (3 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb0]
    simp only [Complex.sub_re, Complex.one_re]
    rcases le_or_gt 0 (1 - s.re) with h | h
    · calc b ^ (1 - s.re) ≤ 2 ^ (1 - s.re) := Real.rpow_le_rpow hb0.le hb2 h
        _ ≤ 2 ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    · calc b ^ (1 - s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hb1 h.le
        _ ≤ 2 ^ (3 / 2 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hB : ‖((b : ℝ) : ℂ) ^ (-s)‖ ≤ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb0, Complex.neg_re]
    rcases le_or_gt (-s.re) 0 with h | h
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hb1 h).trans (by norm_num)
    · calc b ^ (-s.re) ≤ 2 ^ (-s.re) := Real.rpow_le_rpow hb0.le hb2 h.le
        _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
  have hK : ‖emKernel b s‖ ≤ 1 / 4 := by
    refine (norm_emKernel_le hb0 h1).trans ?_
    have : b ^ (-s.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hb1 (by linarith)
    linarith
  refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [norm_div]
    exact div_le_div_of_nonneg_right hA (norm_nonneg _)
  · rw [norm_div, Complex.norm_ofNat]
    linarith
  · rw [norm_mul, norm_mul]
    calc ‖s‖ * ‖s + 1‖ * ‖emKernel b s‖ ≤ ‖s‖ * ‖s + 1‖ * (1 / 4) :=
          mul_le_mul_of_nonneg_left hK (by positivity)
      _ = ‖s‖ * ‖s + 1‖ / 4 := by ring

/-! ### Identification with Mathlib's Hurwitz zeta function -/

/-- **Identity theorem on a punctured half-plane.**  Two functions holomorphic on `Re s > c`
(`c < 1`), except possibly at `s = 1`, that agree on `Re s > 1` agree on `Re s > c`, `s ≠ 1`.  The
two quarter planes `{Re s > c, ± Im s > 0}` are convex and meet `Re s > 1`; the real points follow
by continuity. -/
theorem eq_of_eq_on_one_lt_re {c : ℝ} (hc : c < 1) {f g : ℂ → ℂ}
    (hf : ∀ s : ℂ, c < s.re → s ≠ 1 → DifferentiableAt ℂ f s)
    (hg : ∀ s : ℂ, c < s.re → s ≠ 1 → DifferentiableAt ℂ g s)
    (hright : ∀ s : ℂ, 1 < s.re → f s = g s) {ρ : ℂ} (hρ : c < ρ.re) (hρ1 : ρ ≠ 1) :
    f ρ = g ρ := by
  have hconvex : ∀ U : Set ℂ, IsOpen U → Convex ℝ U → (∀ s ∈ U, c < s.re ∧ s ≠ 1) →
      ∀ z₀ ∈ U, 1 < z₀.re → Set.EqOn f g U := by
    intro U hUo hUc hUs z₀ hz₀U hz₀
    have hfU : AnalyticOnNhd ℂ f U := DifferentiableOn.analyticOnNhd (f := f)
      (fun s hs => (hf s (hUs s hs).1 (hUs s hs).2).differentiableWithinAt) hUo
    have hgU : AnalyticOnNhd ℂ g U := DifferentiableOn.analyticOnNhd (f := g)
      (fun s hs => (hg s (hUs s hs).1 (hUs s hs).2).differentiableWithinAt) hUo
    exact hfU.eqOn_of_preconnected_of_eventuallyEq hgU hUc.isPreconnected hz₀U (by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀]
        with s hs using hright s hs)
  have hre_open : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hupper : Set.EqOn f g ({s : ℂ | c < s.re} ∩ {s : ℂ | 0 < s.im}) :=
    hconvex _ (hre_open.inter (isOpen_lt continuous_const Complex.continuous_im))
      ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _))
      (fun s hs => ⟨hs.1, fun h => by have := hs.2; rw [h] at this; simp at this⟩)
      (2 + I) ⟨by simp; linarith, by simp⟩ (by simp)
  have hlower : Set.EqOn f g ({s : ℂ | c < s.re} ∩ {s : ℂ | s.im < 0}) :=
    hconvex _ (hre_open.inter (isOpen_lt Complex.continuous_im continuous_const))
      ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_lt _))
      (fun s hs => ⟨hs.1, fun h => by have := hs.2; rw [h] at this; simp at this⟩)
      (2 - I) ⟨by simp; linarith, by simp⟩ (by simp)
  rcases lt_trichotomy ρ.im 0 with hlt | heq | hgt
  · exact hlower ⟨hρ, hlt⟩
  · have hcont : ContinuousAt (fun s => f s - g s) ρ :=
      ((hf ρ hρ hρ1).sub (hg ρ hρ hρ1)).continuousAt
    have hpath : Tendsto (fun δ : ℝ => ρ + (δ : ℂ) * I) (𝓝[>] 0) (𝓝 ρ) := by
      have hc : Continuous (fun δ : ℝ => ρ + (δ : ℂ) * I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have h1 := hcont.tendsto.comp hpath
    have h2 : Tendsto (fun δ : ℝ => f (ρ + (δ : ℂ) * I) - g (ρ + (δ : ℂ) * I)) (𝓝[>] 0)
        (𝓝 0) := tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
      rw [hupper ⟨by simpa using hρ, by simpa [heq] using hδ⟩, sub_self])
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h2)
  · exact hupper ⟨hρ, hgt⟩

/-- **The bridge.**  For `0 < a ≤ 1`, `Re s > −½`, `s ≠ 1`:
`ζ(s, a) = a^{−s} + ζ_EM(s, a + 1)`. -/
theorem hurwitzZeta_eq_rpow_add_hurwitzZetaEM {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {s : ℂ}
    (hs : -(1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s =
      ((a : ℝ) : ℂ) ^ (-s) + hurwitzZetaEM (a + 1) s := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0.ne'
  refine eq_of_eq_on_one_lt_re (c := -(1 / 2)) (f := HurwitzZeta.hurwitzZeta (a : UnitAddCircle))
    (g := fun s => ((a : ℝ) : ℂ) ^ (-s) + hurwitzZetaEM (a + 1) s) (by norm_num)
    (fun s _ hs1 => HurwitzZeta.differentiableAt_hurwitzZeta _ hs1)
    (fun s hs hs1 => (differentiableAt_id.neg.const_cpow (Or.inl hane)).add
      (differentiableAt_hurwitzZetaEM (by linarith) hs hs1)) ?_ hs hs1
  intro z hz
  have hsum := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨ha0.le, ha1⟩ hz
  show _ = ((a : ℝ) : ℂ) ^ (-z) + hurwitzZetaEM (a + 1) z
  rw [← hsum.tsum_eq, hsum.summable.tsum_eq_zero_add, hurwitzZetaEM_eq_tsum (by linarith) hz]
  congr 1
  · simp [Complex.cpow_neg]
  · refine tsum_congr fun n => ?_
    rw [one_div, ← Complex.cpow_neg]
    congr 1
    push_cast
    ring

end

end GaloisForLFunctions.HTGeometry
