import GaloisForLFunctions.RHTower.HodgeZetaFlatnessLaw
import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance
import GaloisForLFunctions.RHTower.Reflection

/-!
# The level-`a` Hodge index excludes separated off-line zeros up to the Nyquist height

`HodgeZetaFlatnessLaw` shows that the level-`a` Hodge index forces the leading Taylor coefficient of
`ζ` at every off-line zero below height `2e^{2a-3/4}` to be super-exponentially small. This module
proves the opposite, unconditional, lower bound at every zero that is separated from the others,
and combines the two.

* `abs_log_norm_sub_le`: `log|f|` is `B`-Lipschitz along a segment where `|f'/f| ≤ B`.
* `log_norm_zeta_ge_horizontal`, `abs_log_norm_zeta_vertical_le`: `ζ` is not small along paths at
  distance `δ` from every zero, via `|ζ'/ζ| ≪ log t/δ` (`norm_logDeriv_zeta_le`).
* `exists_height_far_from_finset`: the pigeonhole choice of a height avoiding the zero ordinates.
* `norm_leading_zeta_ge`: at a nontrivial zero `β₀+it₀` (`β₀ > 1/2`, `t₀ ≥ 8`) at distance `≥ d`
  from every other zero, `|v(ρ₀)| ≥ (1/3) exp(-C log(t₀+1)(16(N+1)/d + 1))`, by the minimum
  modulus on the circle of radius `d/2`.
* `riemannXiHat_conj` and `OffLinePairData.norm_u₁_eq`: `Ξ(conj z) = conj Ξ(z)`, so the two nodes
  of an off-line pair carry leading coefficients of equal modulus.

The result (`hodgeIndex_excludes_separated_zero`, `hodgeIndex_nyquist_horizon`): if the Hodge index
holds at level `a ≥ 1`, then every nontrivial zero `ρ₀ = β₀ + it₀` with `β₀ > 1/2`, `t₀ ≥ 8`,
separated by `d` from the other zeros and of order `k`, satisfies

`π e^{2a-3/4} ≤ (π/2) t₀ + 2C log(t₀+1)(16(N+1)/d + 1) + (3k+5)(a-3/8) + a/2 + log(...)`.

So the level-`a` Hodge index excludes every separated off-line zero below height
`2e^{2a-3/4} - O(polylog)`. That is the Nyquist scale, beyond which (by the lattice examples) zero-side
positivity cannot see depth at all. Only super-tight clusters, with another zero within
`O(log² t₀/e^{2a})`, remain.
-/

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-! ## `log |f|` is Lipschitz along a segment where `f'/f` is bounded -/

theorem mem_segment_of_unit {a b : ℂ} {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    a + (r : ℂ) * (b - a) ∈ segment ℝ a b := by
  refine ⟨1 - r, r, by linarith [hr.2], hr.1, by ring, ?_⟩
  simp only [Complex.real_smul]; push_cast; ring

/-- **Logarithmic Lipschitz bound.** If `f` is holomorphic and nonvanishing along the segment
`[a, b]` and `|f'/f| ≤ B` there, then `|log|f(b)| - log|f(a)|| ≤ B |b - a|`. -/
theorem abs_log_norm_sub_le {f : ℂ → ℂ} {a b : ℂ} {B : ℝ}
    (hf : ∀ z ∈ segment ℝ a b, DifferentiableAt ℂ f z) (hne : ∀ z ∈ segment ℝ a b, f z ≠ 0)
    (hB : ∀ z ∈ segment ℝ a b, ‖deriv f z / f z‖ ≤ B) :
    |Real.log ‖f b‖ - Real.log ‖f a‖| ≤ B * ‖b - a‖ := by
  set φ : ℝ → ℂ := fun r => f (a + (r : ℂ) * (b - a)) with hφ
  set g : ℝ → ℝ := fun r => Real.log (‖φ r‖ ^ 2) with hg
  have hφd : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivAt φ (deriv f (a + (r : ℂ) * (b - a)) * (b - a)) r := by
    intro r hr
    have hlin : HasDerivAt (fun r : ℝ => a + (r : ℂ) * (b - a)) (b - a) r := by
      have := ((hasDerivAt_id r).ofReal_comp).mul_const (b - a)
      simpa using this.const_add a
    exact (hf _ (mem_segment_of_unit hr)).hasDerivAt.comp r hlin
  have hφne : ∀ r ∈ Icc (0 : ℝ) 1, φ r ≠ 0 := fun r hr => hne _ (mem_segment_of_unit hr)
  have hgd : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivAt g
      (2 * inner ℝ (φ r) (deriv f (a + (r : ℂ) * (b - a)) * (b - a)) / ‖φ r‖ ^ 2) r := by
    intro r hr
    have h1 := (hφd r hr).norm_sq
    have hpos : ‖φ r‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (hφne r hr))
    exact h1.log hpos
  have hgb : ∀ r ∈ Ico (0 : ℝ) 1,
      ‖2 * inner ℝ (φ r) (deriv f (a + (r : ℂ) * (b - a)) * (b - a)) / ‖φ r‖ ^ 2‖ ≤
        2 * (B * ‖b - a‖) := by
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hr
    have hn : 0 < ‖φ r‖ := norm_pos_iff.mpr (hφne r hr')
    have hin := abs_real_inner_le_norm (φ r) (deriv f (a + (r : ℂ) * (b - a)) * (b - a))
    have hq : ‖deriv f (a + (r : ℂ) * (b - a))‖ ≤ B * ‖φ r‖ := by
      have := hB _ (mem_segment_of_unit hr')
      rw [norm_div, div_le_iff₀ hn] at this
      exact this
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_two, abs_of_pos (by positivity : 0 < ‖φ r‖ ^ 2),
      div_le_iff₀ (by positivity)]
    calc 2 * |inner ℝ (φ r) (deriv f (a + (r : ℂ) * (b - a)) * (b - a))|
        ≤ 2 * (‖φ r‖ * ‖deriv f (a + (r : ℂ) * (b - a)) * (b - a)‖) := by gcongr
      _ = 2 * (‖φ r‖ * (‖deriv f (a + (r : ℂ) * (b - a))‖ * ‖b - a‖)) := by rw [norm_mul]
      _ ≤ 2 * (‖φ r‖ * ((B * ‖φ r‖) * ‖b - a‖)) := by gcongr
      _ = 2 * (B * ‖b - a‖) * ‖φ r‖ ^ 2 := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := g) (a := 0) (b := 1) (C := 2 * (B * ‖b - a‖))
    (fun r hr => (hgd r hr).hasDerivWithinAt) hgb 1 (by simp)
  have h0 : g 0 = 2 * Real.log ‖f a‖ := by
    simp only [hg, hφ]; push_cast; rw [zero_mul, add_zero, Real.log_pow]; push_cast; ring
  have h1 : g 1 = 2 * Real.log ‖f b‖ := by
    simp only [hg, hφ]; push_cast; rw [one_mul, add_sub_cancel, Real.log_pow]; push_cast; ring
  rw [h0, h1, Real.norm_eq_abs, sub_zero, mul_one] at hmv
  have : |2 * Real.log ‖f b‖ - 2 * Real.log ‖f a‖| = 2 * |Real.log ‖f b‖ - Real.log ‖f a‖| := by
    rw [← mul_sub, abs_mul, abs_two]
  rw [this] at hmv
  linarith

/-! ## Symmetry of `Ξ` -/

theorem riemannPhiTransform_eq_xi (s : ℂ) : riemannPhiTransform s = xi s := by
  have h1 : AnalyticOnNhd ℂ riemannPhiTransform univ :=
    fun z _ => differentiable_riemannPhiTransform.analyticAt z
  have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : riemannPhiTransform =ᶠ[𝓝 (2 : ℂ)] xi := by
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
    have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw; linarith
    have hw1 : w ≠ 1 := fun h => by rw [h] at hw; simp at hw
    rw [riemannPhiTransform_eq hw0 hw1, xi_eq_half_mul hw0 hw1]
  exact h1.eqOn_of_preconnected_of_eventuallyEq (xi_analyticOnNhd_univ) isPreconnected_univ
    (mem_univ 2) hev (mem_univ s)

theorem riemannXiHat_eq_xi (z : ℂ) : riemannXiHat z = xi (1 / 2 + I * z) := by
  rw [riemannXiHat_eq, riemannPhiTransform_eq_xi]

/-- `Ξ(conj z) = conj Ξ(z)`: `ξ` is real on the reals and symmetric under `s ↦ 1 - s`. -/
theorem riemannXiHat_conj (z : ℂ) :
    riemannXiHat ((starRingEnd ℂ) z) = (starRingEnd ℂ) (riemannXiHat z) := by
  rw [riemannXiHat_eq_xi, riemannXiHat_eq_xi, ← xi_conj]
  have e : (starRingEnd ℂ) (1 / 2 + I * z) = 1 - (1 / 2 + I * (starRingEnd ℂ) z) := by
    rw [map_add, map_mul, Complex.conj_I, map_div₀, map_one, map_ofNat]; ring
  rw [e, xi_one_sub]

/-- At the mirror node the order and the modulus of the leading coefficient agree. -/
theorem OffLinePairData.norm_u₁_eq (D : OffLinePairData) :
    D.m₁ = D.m₀ ∧ ‖D.u₁ D.γ₁‖ = ‖D.u₀ D.γ₀‖ := by
  set v : ℂ → ℂ := fun z => (starRingEnd ℂ) (D.u₀ ((starRingEnd ℂ) z)) with hv
  have hcv : ContinuousAt v D.γ₁ := by
    have h1 : ContinuousAt (fun z => D.u₀ ((starRingEnd ℂ) z)) D.γ₁ :=
      D.hu₀.continuousAt.comp_of_eq Complex.continuous_conj.continuousAt
        (by simp [OffLinePairData.γ₁])
    exact Complex.continuous_conj.continuousAt.comp h1
  have hv0 : v D.γ₁ ≠ 0 := by
    simp only [hv, OffLinePairData.γ₁, Complex.conj_conj, map_ne_zero]; exact D.hu₀0
  have hloc : riemannXiHat =ᶠ[𝓝 D.γ₁] fun z => (z - D.γ₁) ^ D.m₀ * v z := by
    have hmap : Tendsto (starRingEnd ℂ) (𝓝 D.γ₁) (𝓝 D.γ₀) := by
      have := Complex.continuous_conj.tendsto D.γ₁
      simpa [OffLinePairData.γ₁] using this
    filter_upwards [hmap.eventually D.hloc₀] with z hz
    have e := riemannXiHat_conj ((starRingEnd ℂ) z)
    rw [Complex.conj_conj] at e
    rw [e, hz]
    simp only [hv, map_mul, map_pow, map_sub, Complex.conj_conj, OffLinePairData.γ₁]
  obtain ⟨hm, hu⟩ := local_factor_unique D.hu₁.continuousAt hcv D.hu₁0 hv0 D.hloc₁ hloc
  refine ⟨hm, ?_⟩
  show ‖D.u₁ ((starRingEnd ℂ) D.γ₀)‖ = _
  rw [hu]; simp [hv]

/-! ## Lower bounds for `|ζ|` along zero-free paths -/

theorem xiZeroCopy_mem_carrier (q : XiZeroCopy) : (q.1 : ℂ) ∈ zetaZeroConfig.carrier := by
  have hre0 := xiZeroCopy_re_pos q
  have hre1 := xiZeroCopy_re_lt_one q
  have h0 := xiZeroCopy_ne_zero q
  have h1 := xiZeroCopy_ne_one q
  have hxi := xi_xiZeroCopy_eq_zero q
  rw [xi_eq_xiUnit_mul_zeta h0 h1 hre0] at hxi
  have hζ : riemannZeta (q.1 : ℂ) = 0 :=
    (mul_eq_zero.mp hxi).resolve_left (xiUnit_ne_zero h0 h1 hre0)
  exact ⟨hζ, hre0, hre1⟩

theorem zeta_ne_zero_of_far {s : ℂ} (hσ : 1 / 2 ≤ s.re) {δ : ℝ} (hδ : 0 < δ)
    (hfar : ∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ ‖s - ρ‖) : riemannZeta s ≠ 0 := by
  intro h
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1 h
  · have hmem : s ∈ zetaZeroConfig.carrier := ⟨h, by linarith, h1⟩
    have := hfar s hmem
    rw [sub_self, norm_zero] at this
    linarith

theorem norm_logDeriv_zeta_le_of_far {σ t δ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) (ht : 4 ≤ t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hfar : ∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ ‖((σ : ℂ) + t * I) - ρ‖) :
    ‖logDeriv riemannZeta ((σ : ℂ) + t * I)‖ ≤ logDerivZetaConstant * Real.log t / δ :=
  norm_logDeriv_zeta_le hσ hσ2 ht hδ hδ1 fun q => hfar _ (xiZeroCopy_mem_carrier q)

theorem logDerivZetaConstant_nonneg : 0 ≤ logDerivZetaConstant := by
  unfold logDerivZetaConstant; positivity

/-- **Horizontal path.** If every zero is at distance `≥ δ` from `[σ, 2] + iτ`, then
`log|ζ(σ + iτ)| ≥ log(1/3) - C log τ (2 - σ)/δ`. -/
theorem log_norm_zeta_ge_horizontal {σ τ δ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) (hτ : 4 ≤ τ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hfar : ∀ x ∈ Icc σ 2, ∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ ‖((x : ℂ) + τ * I) - ρ‖) :
    Real.log (1 / 3) - logDerivZetaConstant * Real.log τ / δ * (2 - σ) ≤
      Real.log ‖riemannZeta ((σ : ℂ) + τ * I)‖ := by
  set a : ℂ := (σ : ℂ) + τ * I
  set b : ℂ := ((2 : ℝ) : ℂ) + τ * I
  have hseg : ∀ z ∈ segment ℝ a b, ∃ x ∈ Icc σ 2, z = (x : ℂ) + τ * I := by
    intro z hz
    rw [segment_eq_image] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    refine ⟨(1 - θ) * σ + θ * 2, ⟨by nlinarith [hθ.1, hθ.2], by nlinarith [hθ.1, hθ.2]⟩, ?_⟩
    simp only [a, b, Complex.real_smul]; push_cast; ring
  have hB : ∀ z ∈ segment ℝ a b,
      ‖deriv riemannZeta z / riemannZeta z‖ ≤ logDerivZetaConstant * Real.log τ / δ := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hseg z hz
    exact norm_logDeriv_zeta_le_of_far (by linarith [hx.1]) hx.2 hτ hδ hδ1 (hfar x hx)
  have hne : ∀ z ∈ segment ℝ a b, riemannZeta z ≠ 0 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hseg z hz
    exact zeta_ne_zero_of_far (by simp; linarith [hx.1]) hδ (hfar x hx)
  have hd : ∀ z ∈ segment ℝ a b, DifferentiableAt ℂ riemannZeta z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hseg z hz
    refine differentiableAt_riemannZeta fun h => ?_
    have := congrArg Complex.im h; simp at this; linarith
  have hlip := abs_log_norm_sub_le hd hne hB
  have hba : ‖b - a‖ = 2 - σ := by
    simp only [a, b]
    rw [show ((2 : ℝ) : ℂ) + τ * I - ((σ : ℂ) + τ * I) = ((2 - σ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hba] at hlip
  have h3 : Real.log (1 / 3) ≤ Real.log ‖riemannZeta b‖ :=
    Real.log_le_log (by norm_num) (norm_riemannZeta_ge_third (by simp [b]))
  have := (abs_le.mp hlip).2
  linarith

/-- **Vertical path.** If every zero is at distance `≥ δ` from `σ + i[τ₁, τ₂]`, then
`|log|ζ(σ+iτ₂)| - log|ζ(σ+iτ₁)|| ≤ C log τ₂ (τ₂ - τ₁)/δ`. -/
theorem abs_log_norm_zeta_vertical_le {σ τ₁ τ₂ δ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2)
    (hτ : 4 ≤ τ₁) (h12 : τ₁ ≤ τ₂) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hfar : ∀ y ∈ Icc τ₁ τ₂, ∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ ‖((σ : ℂ) + y * I) - ρ‖) :
    |Real.log ‖riemannZeta ((σ : ℂ) + τ₂ * I)‖ - Real.log ‖riemannZeta ((σ : ℂ) + τ₁ * I)‖| ≤
      logDerivZetaConstant * Real.log τ₂ / δ * (τ₂ - τ₁) := by
  set a : ℂ := (σ : ℂ) + τ₁ * I
  set b : ℂ := (σ : ℂ) + τ₂ * I
  have hseg : ∀ z ∈ segment ℝ a b, ∃ y ∈ Icc τ₁ τ₂, z = (σ : ℂ) + y * I := by
    intro z hz
    rw [segment_eq_image] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    refine ⟨(1 - θ) * τ₁ + θ * τ₂, ⟨by nlinarith [hθ.1, hθ.2], by nlinarith [hθ.1, hθ.2]⟩, ?_⟩
    simp only [a, b, Complex.real_smul]; push_cast; ring
  have hB : ∀ z ∈ segment ℝ a b,
      ‖deriv riemannZeta z / riemannZeta z‖ ≤ logDerivZetaConstant * Real.log τ₂ / δ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hseg z hz
    refine (norm_logDeriv_zeta_le_of_far hσ hσ2 (by linarith [hy.1]) hδ hδ1 (hfar y hy)).trans ?_
    have := logDerivZetaConstant_nonneg
    gcongr
    · linarith [hy.1]
    · exact hy.2
  have hne : ∀ z ∈ segment ℝ a b, riemannZeta z ≠ 0 := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hseg z hz
    exact zeta_ne_zero_of_far (by simp; linarith) hδ (hfar y hy)
  have hd : ∀ z ∈ segment ℝ a b, DifferentiableAt ℂ riemannZeta z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hseg z hz
    refine differentiableAt_riemannZeta fun h => ?_
    have := congrArg Complex.im h; simp at this; linarith [hy.1]
  have hlip := abs_log_norm_sub_le hd hne hB
  have hba : ‖b - a‖ = τ₂ - τ₁ := by
    simp only [a, b]
    rw [show (σ : ℂ) + τ₂ * I - ((σ : ℂ) + τ₁ * I) = ((τ₂ - τ₁ : ℝ) : ℂ) * I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  rw [hba] at hlip
  exact hlip

/-- **Pigeonhole for heights.** Among `n` reals, some point of any interval of length `L` is at
distance `≥ L/(2(n+1))` from all of them. -/
theorem exists_height_far_from_finset (Y : Finset ℝ) (u : ℝ) {L : ℝ} (hL : 0 < L) :
    ∃ τ ∈ Icc u (u + L), ∀ y ∈ Y, L / (2 * (Y.card + 1)) ≤ |τ - y| := by
  classical
  set n := Y.card
  set η : ℝ := L / (2 * (n + 1)) with hη
  by_contra hcon
  push Not at hcon
  -- candidates `u + j L/(n+1)` for `j = 0..n+1`
  set c : ℕ → ℝ := fun j => u + j * (L / (n + 1)) with hc
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hmem : ∀ j ∈ Finset.range (n + 2), c j ∈ Icc u (u + L) := by
    intro j hj
    have hj' : (j : ℝ) ≤ n + 1 := by
      have := Finset.mem_range.mp hj; exact_mod_cast (by omega : j ≤ n + 1)
    constructor
    · have : 0 ≤ (j : ℝ) * (L / (n + 1)) := by positivity
      simp only [hc]; linarith
    · simp only [hc]
      have : (j : ℝ) * (L / (n + 1)) ≤ (n + 1) * (L / (n + 1)) :=
        mul_le_mul_of_nonneg_right hj' (by positivity)
      rw [mul_div_cancel₀ _ hn1.ne'] at this
      linarith
  have hpick : ∀ j ∈ Finset.range (n + 2), ∃ y ∈ Y, |c j - y| < η := fun j hj =>
    hcon (c j) (hmem j hj)
  choose! f hfY hfη using hpick
  have hinj : Set.InjOn f ↑(Finset.range (n + 2)) := by
    intro i hi j hj hij
    by_contra hne
    have h1 := hfη i hi
    have h2 := hfη j hj
    rw [hij] at h1
    have hdist : |c i - c j| < 2 * η := by
      calc |c i - c j| = |(c i - f j) - (c j - f j)| := by ring_nf
        _ ≤ |c i - f j| + |c j - f j| := abs_sub _ _
        _ < η + η := add_lt_add h1 h2
        _ = 2 * η := by ring
    have hsep : L / (n + 1) ≤ |c i - c j| := by
      simp only [hc]
      rw [show u + (i : ℝ) * (L / (n + 1)) - (u + (j : ℝ) * (L / (n + 1))) =
        ((i : ℝ) - j) * (L / (n + 1)) by ring, abs_mul, abs_of_pos (div_pos hL hn1)]
      have : (1 : ℝ) ≤ |(i : ℝ) - j| := by
        rcases lt_or_gt_of_ne hne with h | h
        · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
          rw [abs_of_neg (by linarith)]; linarith
        · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]; linarith
      nlinarith [(by positivity : (0 : ℝ) ≤ L / (n + 1))]
    have : 2 * η = L / (n + 1) := by rw [hη]; field_simp
    linarith
  have hcard := Finset.card_le_card_of_injOn f (fun j hj => hfY j hj) hinj
  simp at hcard
  omega

/-! ## Lower bound for the leading coefficient of `ζ` at a separated zero -/

/-- The ordinates of the zeros with `t₀ - 3 < γ ≤ t₀ + 3`. -/
def windowOrdinates (t₀ : ℝ) : Finset ℝ :=
  ((zetaZeroConfig.finite_window (t₀ - 3) (t₀ + 3)).toFinset).image Complex.im

theorem mem_windowOrdinates {t₀ : ℝ} {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier)
    (h : |ρ.im - t₀| ≤ 2) : ρ.im ∈ windowOrdinates t₀ := by
  unfold windowOrdinates
  refine Finset.mem_image.mpr ⟨ρ, ?_, rfl⟩
  rw [Set.Finite.mem_toFinset]
  exact ⟨hρ, by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩

/-- On the circle of radius `d/2` around a `d`-separated zero `β₀ + it₀` (`β₀ > 1/2`, `t₀ ≥ 8`),
`|ζ| ≥ (1/3) exp(-C log(t₀+1)(16(N+1)/d + 1))`. The path goes up to a height avoiding every zero
ordinate by `d/(8(N+1))`, then right to `Re s = 2`. -/
theorem norm_zeta_ge_on_circle {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (hβ : 1 / 2 < ρ₀.re) (ht : 8 ≤ ρ₀.im) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → d ≤ ‖ρ - ρ₀‖)
    (hdep : d ≤ 2 * ρ₀.re - 1) {s : ℂ} (hs : ‖s - ρ₀‖ = d / 2) :
    (1 / 3) * Real.exp (-(logDerivZetaConstant * Real.log (ρ₀.im + 1) *
      (16 * ((windowOrdinates ρ₀.im).card + 1) / d + 1))) ≤ ‖riemannZeta s‖ := by
  set t₀ := ρ₀.im with ht₀
  set β₀ := ρ₀.re with hβ₀
  set N : ℕ := (windowOrdinates t₀).card with hN
  set r : ℝ := d / 2 with hr
  have hr0 : 0 < r := by positivity
  set C := logDerivZetaConstant with hC
  have hC0 : 0 ≤ C := logDerivZetaConstant_nonneg
  have hβ1 : β₀ < 1 := by have h : IsNontrivialZero ρ₀ := hρ₀; exact h.2.2
  have hre : |s.re - β₀| ≤ r := by
    have := Complex.abs_re_le_norm (s - ρ₀); rw [Complex.sub_re] at this; linarith
  have him : |s.im - t₀| ≤ r := by
    have := Complex.abs_im_le_norm (s - ρ₀); rw [Complex.sub_im] at this; linarith
  have hσ1 : 1 / 2 ≤ s.re := by have := (abs_le.mp hre).1; linarith
  have hσ2 : s.re ≤ 2 := by have := (abs_le.mp hre).2; linarith
  have hrd : r ≤ 1 / 2 := by rw [hr]; linarith
  obtain ⟨τ', hτ', hgood⟩ := exists_height_far_from_finset (windowOrdinates t₀) s.im (L := r / 2)
    (by positivity)
  have hτ'lo : s.im ≤ τ' := hτ'.1
  have hτ'hi : τ' ≤ s.im + r / 2 := hτ'.2
  have hs4 : 4 ≤ s.im := by linarith [(abs_le.mp him).1]
  have hτt : |τ' - t₀| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [(abs_le.mp him).1, (abs_le.mp him).2]
  set δh : ℝ := d / (8 * (N + 1)) with hδh
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hδh0 : 0 < δh := by positivity
  have hδh1 : δh ≤ 1 := by rw [hδh, div_le_one (by positivity)]; nlinarith
  have hδhd : δh ≤ d / 4 := by
    rw [hδh, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  -- the horizontal path at height `τ'`
  have hfarh : ∀ x ∈ Icc s.re 2, ∀ ρ ∈ zetaZeroConfig.carrier,
      δh ≤ ‖((x : ℂ) + τ' * I) - ρ‖ := by
    intro x _ ρ hρ
    have hi := Complex.abs_im_le_norm (((x : ℂ) + τ' * I) - ρ)
    have eim : (((x : ℂ) + τ' * I) - ρ).im = τ' - ρ.im := by simp
    rw [eim] at hi
    refine le_trans ?_ hi
    by_cases hw : |ρ.im - t₀| ≤ 2
    · have := hgood _ (mem_windowOrdinates hρ hw)
      have e : r / 2 / (2 * ((windowOrdinates t₀).card + 1)) = δh := by
        rw [hδh, hr]; field_simp; ring
      rw [e] at this; exact this
    · push Not at hw
      have : 1 ≤ |τ' - ρ.im| := by
        have h1 : |ρ.im - t₀| ≤ |ρ.im - τ'| + |τ' - t₀| := by
          calc |ρ.im - t₀| = |(ρ.im - τ') + (τ' - t₀)| := by ring_nf
            _ ≤ |ρ.im - τ'| + |τ' - t₀| := abs_add_le _ _
        rw [abs_sub_comm ρ.im τ'] at h1; linarith
      linarith
  have hτ'4 : 4 ≤ τ' := by linarith
  have hH := log_norm_zeta_ge_horizontal hσ1 hσ2 hτ'4 hδh0 hδh1 hfarh
  -- the vertical path from `s` to `Re s + iτ'`
  have hfarv : ∀ y ∈ Icc s.im τ', ∀ ρ ∈ zetaZeroConfig.carrier,
      d / 4 ≤ ‖((s.re : ℂ) + y * I) - ρ‖ := by
    intro y hy ρ hρ
    have hw : ‖((s.re : ℂ) + y * I) - s‖ ≤ r / 2 := by
      have e : ((s.re : ℂ) + y * I) - s = ((y - s.im : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp
      rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hy.1])]
      linarith [hy.2]
    by_cases hρρ : ρ = ρ₀
    · subst hρρ
      have := norm_sub_norm_le (s - ρ) (s - ((s.re : ℂ) + y * I))
      rw [show s - ρ - (s - ((s.re : ℂ) + y * I)) = ((s.re : ℂ) + y * I) - ρ by ring,
        norm_sub_rev s ((s.re : ℂ) + y * I)] at this
      rw [hs] at this
      rw [hr] at this hw
      linarith
    · have h1 := hsep ρ hρ hρρ
      have h2 : ‖ρ - ρ₀‖ ≤ ‖((s.re : ℂ) + y * I) - ρ‖ + ‖((s.re : ℂ) + y * I) - s‖ + ‖s - ρ₀‖ := by
        calc ‖ρ - ρ₀‖ = ‖(ρ - ((s.re : ℂ) + y * I)) + (((s.re : ℂ) + y * I) - s) + (s - ρ₀)‖ := by
              ring_nf
          _ ≤ ‖ρ - ((s.re : ℂ) + y * I)‖ + ‖((s.re : ℂ) + y * I) - s‖ + ‖s - ρ₀‖ :=
              norm_add₃_le
          _ = _ := by rw [norm_sub_rev ρ]
      rw [hs, hr] at h2; rw [hr] at hw
      linarith
  have hsre : (s.re : ℂ) + s.im * I = s := Complex.re_add_im s
  have hV := abs_log_norm_zeta_vertical_le hσ1 hσ2 hs4 hτ'lo (by linarith : (0 : ℝ) < d / 4)
    (by linarith) hfarv
  rw [hsre] at hV
  -- combine the two paths
  have hlogτ : Real.log τ' ≤ Real.log (t₀ + 1) :=
    Real.log_le_log (by linarith) (by linarith [(abs_le.mp hτt).2])
  have hlog0 : 0 ≤ Real.log τ' := Real.log_nonneg (by linarith)
  have hHb : Real.log (1 / 3) - C * Real.log (t₀ + 1) * (16 * (N + 1) / d) ≤
      Real.log ‖riemannZeta ((s.re : ℂ) + τ' * I)‖ := by
    refine le_trans ?_ hH
    have hlen : 2 - s.re ≤ 2 := by linarith
    have e : C * Real.log τ' / δh * (2 - s.re) ≤ C * Real.log (t₀ + 1) * (16 * (N + 1) / d) := by
      rw [hδh]
      have hq : C * Real.log τ' / (d / (8 * (N + 1))) = C * Real.log τ' * (8 * (N + 1) / d) := by
        field_simp
      rw [hq]
      have h8 : 0 ≤ 8 * ((N : ℝ) + 1) / d := div_nonneg (by positivity) hd.le
      have hl1 : 0 ≤ Real.log (t₀ + 1) := Real.log_nonneg (by linarith)
      calc C * Real.log τ' * (8 * (N + 1) / d) * (2 - s.re)
          ≤ C * Real.log (t₀ + 1) * (8 * (N + 1) / d) * 2 := by
            apply mul_le_mul _ hlen (by linarith) (mul_nonneg (mul_nonneg hC0 hl1) h8)
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogτ hC0) h8
        _ = C * Real.log (t₀ + 1) * (16 * (N + 1) / d) := by ring
    linarith
  have hVb : C * Real.log τ' / (d / 4) * (τ' - s.im) ≤ C * Real.log (t₀ + 1) := by
    have hq : C * Real.log τ' / (d / 4) * (τ' - s.im) ≤ C * Real.log τ' / (d / 4) * (d / 4) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (mul_nonneg hC0 hlog0) (by linarith))
      rw [hr] at hτ'hi; linarith
    have e : C * Real.log τ' / (d / 4) * (d / 4) = C * Real.log τ' := by
      field_simp
    rw [e] at hq
    have := mul_le_mul_of_nonneg_left hlogτ hC0
    linarith
  have hlogfinal : Real.log (1 / 3) - C * Real.log (t₀ + 1) * (16 * (N + 1) / d + 1) ≤
      Real.log ‖riemannZeta s‖ := by
    rw [← hC] at hV
    have := (abs_le.mp hV).2
    nlinarith
  have hζ0 : riemannZeta s ≠ 0 := by
    refine zeta_ne_zero_of_far hσ1 (by linarith : (0 : ℝ) < d / 4) fun ρ hρ => ?_
    have := hfarv s.im ⟨le_rfl, hτ'lo⟩ ρ hρ
    rwa [hsre] at this
  have hpos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hζ0
  calc (1 / 3) * Real.exp (-(C * Real.log (t₀ + 1) * (16 * (N + 1) / d + 1)))
      = Real.exp (Real.log (1 / 3) - C * Real.log (t₀ + 1) * (16 * (N + 1) / d + 1)) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (Real.log ‖riemannZeta s‖) := Real.exp_le_exp.mpr hlogfinal
    _ = ‖riemannZeta s‖ := Real.exp_log hpos

/-- The separation from the mirror zero bounds `d` by twice the depth. -/
theorem sep_le_depth {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hβ : 1 / 2 < ρ₀.re) {d : ℝ}
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → d ≤ ‖ρ - ρ₀‖) : d ≤ 2 * ρ₀.re - 1 := by
  have hmem := zetaZeroConfig.reflect_mem ρ₀ hρ₀
  have hne : Zeta23.reflect ρ₀ ≠ ρ₀ := by
    intro h; have := congrArg Complex.re h; simp [Zeta23.reflect] at this; linarith
  have h := hsep _ hmem hne
  have e : Zeta23.reflect ρ₀ - ρ₀ = ((1 - 2 * ρ₀.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Zeta23.reflect]; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)] at h
  linarith

/-- **Lower bound for the leading coefficient at a separated zero.** For a nontrivial zero
`ρ₀ = β₀ + it₀` with `β₀ > 1/2`, `t₀ ≥ 8`, at distance `≥ d > 0` from every other zero, with
`ζ(s) = (s - ρ₀)^k v(s)` near `ρ₀`:
`|v(ρ₀)| ≥ (1/3) exp(-C log(t₀+1)(16(N+1)/d + 1))`, `N` the number of zero ordinates near `t₀`.
Minimum modulus on the circle of radius `d/2`. -/
theorem norm_leading_zeta_ge {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (hβ : 1 / 2 < ρ₀.re) (ht : 8 ≤ ρ₀.im) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → d ≤ ‖ρ - ρ₀‖)
    {k : ℕ} {v : ℂ → ℂ} (hv : AnalyticAt ℂ v ρ₀) (hv0 : v ρ₀ ≠ 0)
    (hloc : ∀ᶠ s in 𝓝 ρ₀, riemannZeta s = (s - ρ₀) ^ k * v s) :
    (1 / 3) * Real.exp (-(logDerivZetaConstant * Real.log (ρ₀.im + 1) *
      (16 * ((windowOrdinates ρ₀.im).card + 1) / d + 1))) ≤ ‖v ρ₀‖ := by
  classical
  set m := (1 / 3) * Real.exp (-(logDerivZetaConstant * Real.log (ρ₀.im + 1) *
    (16 * ((windowOrdinates ρ₀.im).card + 1) / d + 1))) with hm
  have hm0 : 0 < m := by positivity
  have hdep := sep_le_depth hρ₀ hβ hsep
  set r : ℝ := d / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r ≤ 1 / 2 := by
    have : ρ₀.re < 1 := by have h : IsNontrivialZero ρ₀ := hρ₀; exact h.2.2
    rw [hr]; linarith
  set g : ℂ → ℂ := fun s => if s = ρ₀ then v ρ₀ else riemannZeta s / (s - ρ₀) ^ k with hg
  have hgv : g =ᶠ[𝓝 ρ₀] v := by
    filter_upwards [hloc] with s hs
    simp only [hg]
    split_ifs with h
    · rw [h]
    · rw [hs, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.mpr h))]
  -- points of the closed ball
  have hball : ∀ s ∈ closedBall ρ₀ r, 1 / 2 ≤ s.re ∧ 4 ≤ s.im ∧ s ≠ 1 := by
    intro s hs
    have hn : ‖s - ρ₀‖ ≤ r := by simpa [dist_eq_norm] using hs
    have hre := Complex.abs_re_le_norm (s - ρ₀)
    have him := Complex.abs_im_le_norm (s - ρ₀)
    rw [Complex.sub_re] at hre; rw [Complex.sub_im] at him
    have h1 : 1 / 2 ≤ s.re := by have := (abs_le.mp (hre.trans hn)).1; linarith
    have h2 : 4 ≤ s.im := by have := (abs_le.mp (him.trans hn)).1; linarith
    exact ⟨h1, h2, fun h => by rw [h] at h2; simp at h2; linarith⟩
  have hdiff : ∀ s ∈ closedBall ρ₀ r, DifferentiableAt ℂ g s := by
    intro s hs
    by_cases hsρ : s = ρ₀
    · subst hsρ; exact (hv.differentiableAt).congr_of_eventuallyEq hgv
    · have hev : g =ᶠ[𝓝 s] fun w => riemannZeta w / (w - ρ₀) ^ k := by
        filter_upwards [eventually_ne_nhds hsρ] with w hw
        simp only [hg, if_neg hw]
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      exact (differentiableAt_riemannZeta (hball s hs).2.2).div (by fun_prop)
        (pow_ne_zero _ (sub_ne_zero.mpr hsρ))
  have hne : ∀ s ∈ closedBall ρ₀ r, g s ≠ 0 := by
    intro s hs
    by_cases hsρ : s = ρ₀
    · subst hsρ; simp only [hg, if_pos rfl]; exact hv0
    · simp only [hg, if_neg hsρ]
      refine div_ne_zero ?_ (pow_ne_zero _ (sub_ne_zero.mpr hsρ))
      have hn : ‖s - ρ₀‖ ≤ r := by simpa [dist_eq_norm] using hs
      have hpos : 0 < ‖s - ρ₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsρ)
      refine zeta_ne_zero_of_far (hball s hs).1 (lt_min hpos (by rw [hr]; linarith :
        (0 : ℝ) < d - r)) fun ρ hρ => ?_
      by_cases hρρ : ρ = ρ₀
      · rw [hρρ]; exact min_le_left _ _
      · refine (min_le_right _ _).trans ?_
        have h1 := hsep ρ hρ hρρ
        have h2 : ‖ρ - ρ₀‖ ≤ ‖s - ρ‖ + ‖s - ρ₀‖ := by
          calc ‖ρ - ρ₀‖ = ‖(s - ρ₀) - (s - ρ)‖ := by ring_nf
            _ ≤ ‖s - ρ₀‖ + ‖s - ρ‖ := norm_sub_le _ _
            _ = ‖s - ρ‖ + ‖s - ρ₀‖ := by ring
        linarith
  -- maximum modulus for `1/g`
  have hdc : DiffContOnCl ℂ (fun s => (g s)⁻¹) (ball ρ₀ r) := by
    have hdo : DifferentiableOn ℂ (fun s => (g s)⁻¹) (closedBall ρ₀ r) := fun s hs =>
      ((hdiff s hs).inv (hne s hs)).differentiableWithinAt
    exact ⟨hdo.mono ball_subset_closedBall, hdo.continuousOn.mono closure_ball_subset_closedBall⟩
  have hfront : ∀ z ∈ frontier (ball ρ₀ r), ‖(g z)⁻¹‖ ≤ m⁻¹ := by
    intro z hz
    rw [frontier_ball ρ₀ hr0.ne'] at hz
    have hzn : ‖z - ρ₀‖ = r := by simpa [dist_eq_norm] using hz
    have hzρ : z ≠ ρ₀ := by intro h; rw [h, sub_self, norm_zero] at hzn; linarith
    have hlow := norm_zeta_ge_on_circle hρ₀ hβ ht hd hsep hdep (s := z) (by rw [hzn])
    simp only [hg, if_neg hzρ, norm_inv, norm_div, norm_pow, hzn]
    rw [inv_div]
    have hζpos : 0 < ‖riemannZeta z‖ := lt_of_lt_of_le hm0 hlow
    rw [div_le_iff₀ hζpos]
    have hrk : r ^ k ≤ 1 := pow_le_one₀ hr0.le (by linarith)
    calc r ^ k ≤ 1 := hrk
      _ = m⁻¹ * m := (inv_mul_cancel₀ hm0.ne').symm
      _ ≤ m⁻¹ * ‖riemannZeta z‖ := by gcongr
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hfront
    (subset_closure (mem_ball_self hr0))
  have hgρ : g ρ₀ = v ρ₀ := by simp [hg]
  rw [hgρ, norm_inv] at hmax
  have hvpos : 0 < ‖v ρ₀‖ := norm_pos_iff.mpr hv0
  rw [inv_le_inv₀ hvpos hm0] at hmax
  exact hmax

/-! ## The exclusion law -/

local notation "Φ" => riemannPhiKernel
local notation "Mθ" => jacobiThetaTailConstant

/-- The tail of `Φ` at level `a` with weight `1/2 + 3k`, explicitly. -/
theorem expTail_riemannPhiKernel_level_le {a : ℝ} (ha : 1 ≤ a) (k : ℕ)
    (hlam : 1 / 2 + 3 * (k : ℝ) + 11 / 2 ≤ 2 * π * Real.exp (2 * (a - 3 / 8))) :
    expTail Φ (1 / 2 + 3 / 2 * ((2 * k : ℕ) : ℝ)) (a - 3 / 8) ≤
      (80 * Mθ * Real.exp π + 1) * Real.exp ((1 / 2 + 3 * (k : ℝ) + 9 / 2) * (a - 3 / 8) -
        π * Real.exp (2 * (a - 3 / 8))) := by
  have hM : 0 ≤ Mθ := jacobiThetaTailConstant_nonneg
  have hX3 : 3 ≤ Real.exp (2 * (a - 3 / 8)) := by
    have := Real.quadratic_le_exp_of_nonneg (x := 2 * (a - 3 / 8)) (by linarith)
    nlinarith
  have hlamk : (1 / 2 + 3 / 2 * ((2 * k : ℕ) : ℝ)) = 1 / 2 + 3 * (k : ℝ) := by push_cast; ring
  rw [hlamk]
  have htail := expTail_riemannPhiKernel_le (c := 1 / 2 + 3 * (k : ℝ)) hX3 (by linarith)
  obtain ⟨E', hE'⟩ : ∃ E', E' = Real.exp ((1 / 2 + 3 * (k : ℝ) + 9 / 2) * (a - 3 / 8) -
      π * Real.exp (2 * (a - 3 / 8))) := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = 2 * π * Real.exp (2 * (a - 3 / 8)) - (1 / 2 + 3 * (k : ℝ)) - 9 / 2 :=
    ⟨_, rfl⟩
  rw [← hE', ← hκ] at htail
  rw [← hE']
  have hκ1 : 1 ≤ κ := by rw [hκ]; linarith
  have hE'0 : 0 < E' := by rw [hE']; exact Real.exp_pos _
  obtain ⟨A, hA⟩ : ∃ A, A = 80 * Mθ * Real.exp π := ⟨_, rfl⟩
  rw [← hA] at htail ⊢
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine htail.trans ?_
  rw [div_le_iff₀ (by linarith)]
  have h1 : A * E' ≤ (A + 1) * E' := by nlinarith
  have h2 : (A + 1) * E' ≤ (A + 1) * E' * κ :=
    le_mul_of_one_le_right (by positivity) hκ1
  linarith

/-- **Nyquist exclusion law.** There is an absolute constant `K` with the following property. Let
the level-`a` Hodge index hold (`a ≥ 1`). Let `ρ₀ = β₀ + it₀` be a nontrivial zero with
`β₀ > 1/2`, `t₀ ≥ 8`, at distance `≥ d > 0` from every other zero, with `ζ(s) = (s-ρ₀)^k v(s)`
near `ρ₀`. Put `λ = 1/2 + 3k` and `X = a - 3/8`, and assume `λ + 11/2 ≤ 2πe^{2X}`. Then

`(β₀(1-β₀))² e^{-πt₀/2} m² ≤ K 16^k (1 + 1/|β₀-½|)² (1+|γ₀|)² e^{a/2} G_Φ(2k) e^{(λ+9/2)X - πe^{2X}}`,

where `m = (1/3) exp(-C log(t₀+1)(16(N+1)/d + 1))` is the unconditional lower bound for `|v(ρ₀)|`.
The left side is `≈ e^{-πt₀/2}` and the right side is `≈ e^{-πe^{2X}}`, so the inequality fails for
`t₀ < 2e^{2a-3/4} - O(polylog)`: the Hodge index at level `a` excludes every separated off-line
zero below that height. -/
theorem hodgeIndex_excludes_separated_zero :
    ∃ K : ℝ, 0 < K ∧ ∀ {a : ℝ}, 1 ≤ a → HodgeIndexAtLevel zetaZeroConfig a →
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → 1 / 2 < ρ₀.re → 8 ≤ ρ₀.im →
      ∀ {d : ℝ}, 0 < d → (∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → d ≤ ‖ρ - ρ₀‖) →
      ∀ {k : ℕ} {v : ℂ → ℂ}, AnalyticAt ℂ v ρ₀ → v ρ₀ ≠ 0 →
        (∀ᶠ s in 𝓝 ρ₀, riemannZeta s = (s - ρ₀) ^ k * v s) →
        1 / 2 + 3 * (k : ℝ) + 11 / 2 ≤ 2 * π * Real.exp (2 * (a - 3 / 8)) →
        (ρ₀.re * (1 - ρ₀.re)) ^ 2 * Real.exp (-(π * ρ₀.im / 2)) *
            ((1 / 3) * Real.exp (-(logDerivZetaConstant * Real.log (ρ₀.im + 1) *
              (16 * ((windowOrdinates ρ₀.im).card + 1) / d + 1)))) ^ 2 ≤
          K * 16 ^ k * (1 + 1 / |ρ₀.re - 1 / 2|) ^ 2 * (1 + ‖gammaOf ρ₀‖) ^ 2 *
            Real.exp (a / 2) * expTail Φ (1 / 2 + 3 / 2 * ((2 * k : ℕ) : ℝ)) 0 *
            Real.exp ((1 / 2 + 3 * (k : ℝ) + 9 / 2) * (a - 3 / 8) -
              π * Real.exp (2 * (a - 3 / 8))) := by
  obtain ⟨C, hC, hflat⟩ := OffLinePairData.flatness
  have hM : 0 ≤ Mθ := jacobiThetaTailConstant_nonneg
  refine ⟨128 ^ 2 * C * (80 * Mθ * Real.exp π + 1), by positivity, fun {a} ha hH {ρ₀} hρ₀ hβ ht
    {d} hd hsep {k v} hv hv0 hloc hlam => ?_⟩
  have hnt : IsNontrivialZero ρ₀ := hρ₀
  have hoff : ρ₀.re ≠ 1 / 2 := ne_of_gt hβ
  obtain ⟨D, hD⟩ := OffLinePairData.exists_offLinePairData hρ₀ hoff
  -- transfer and symmetry
  have hloc₀ : riemannXiHat =ᶠ[𝓝 (gammaOf ρ₀)] fun z => (z - gammaOf ρ₀) ^ D.m₀ * D.u₀ z := by
    rw [← hD]; exact D.hloc₀
  have hu₀ : AnalyticAt ℂ D.u₀ (gammaOf ρ₀) := by rw [← hD]; exact D.hu₀
  have hu₀0 : D.u₀ (gammaOf ρ₀) ≠ 0 := by rw [← hD]; exact D.hu₀0
  obtain ⟨hm₀, hn₀⟩ := norm_leading_riemannXiHat hρ₀ hv hv0 hloc hu₀ hu₀0 hloc₀
  rw [← hD] at hn₀
  obtain ⟨hm₁, hn₁⟩ := D.norm_u₁_eq
  have hn : D.n = 2 * k := by unfold OffLinePairData.n; rw [hm₁, hm₀]; ring
  -- the flatness law
  have hF := hflat D hρ₀ hD.symm ha hH
  rw [hn] at hF
  -- lower bounds
  have hβim : D.γ₀.im = 1 / 2 - ρ₀.re := by rw [hD, WeilEF.gammaOf_im]
  have hP : ∀ z : ℂ, z.im = D.γ₀.im ∨ z.im = -D.γ₀.im →
      ρ₀.re * (1 - ρ₀.re) / 128 ≤ ‖polarSymbol OffLinePairData.sh z‖ := by
    intro z hz
    have hzi : |z.im| ≤ 1 / 2 := by
      rcases hz with h | h
      · rw [h]; exact D.him2
      · rw [h, abs_neg]; exact D.him2
    have h := norm_polarSymbol_ge (s := OffLinePairData.sh) OffLinePairData.sh_pos.le hzi
    have hsq : z.im ^ 2 = D.γ₀.im ^ 2 := by rcases hz with h | h <;> rw [h]; ring
    rw [hsq, hβim] at h
    have e : OffLinePairData.sh ^ 2 * (1 - 4 * (1 / 2 - ρ₀.re) ^ 2) / 8 =
        ρ₀.re * (1 - ρ₀.re) / 128 := by rw [show OffLinePairData.sh = 1 / 8 from rfl]; ring
    linarith
  have hP₀ := hP D.γ₀ (Or.inl rfl)
  have hP₁ := hP D.γ₁ (Or.inr (by simp [OffLinePairData.γ₁]))
  have hk₀ := norm_kernel_at_γ₀_ge D
  have hk₁ := norm_kernel_at_γ₁_ge D
  have hxi := exp_le_norm_xiUnit hnt.2.1 hnt.2.2 (by rw [abs_of_pos (by linarith)]; exact ht)
  rw [abs_of_pos (by linarith : (0 : ℝ) < ρ₀.im)] at hxi
  have hlow := norm_leading_zeta_ge hρ₀ hβ ht hd hsep hv hv0 hloc
  set mv := (1 / 3) * Real.exp (-(logDerivZetaConstant * Real.log (ρ₀.im + 1) *
    (16 * ((windowOrdinates ρ₀.im).card + 1) / d + 1))) with hmv
  have hmv0 : 0 ≤ mv := by positivity
  set E := Real.exp (-(π * ρ₀.im / 4)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hu₀low : E * mv ≤ ‖D.u₀ D.γ₀‖ := by
    rw [hn₀]; exact mul_le_mul hxi hlow hmv0 (norm_nonneg _)
  have hu₁low : E * mv ≤ ‖D.u₁ D.γ₁‖ := by rw [hn₁]; exact hu₀low
  have hq : 0 ≤ ρ₀.re * (1 - ρ₀.re) / 128 := by
    have : ρ₀.re < 1 := hnt.2.2; nlinarith
  have hX : (ρ₀.re * (1 - ρ₀.re) / 128 * (E * mv)) * (ρ₀.re * (1 - ρ₀.re) / 128 * (E * mv)) ≤
      ‖polarSymbol OffLinePairData.sh D.γ₀ * paperFT D.kernel D.γ₀‖ *
        ‖polarSymbol OffLinePairData.sh D.γ₁ * paperFT D.kernel D.γ₁‖ := by
    rw [norm_mul, norm_mul]
    have h0 : 0 ≤ E * mv := by positivity
    gcongr
    · exact hu₀low.trans hk₀
    · exact hu₁low.trans hk₁
  -- the tail of `Φ`
  have htail' := expTail_riemannPhiKernel_level_le ha k hlam
  have hsh : a - 1 / 4 - OffLinePairData.sh = a - 3 / 8 := by
    rw [show OffLinePairData.sh = 1 / 8 from rfl]; ring
  rw [hsh] at hF
  have himγ : |D.γ₀.im| = |ρ₀.re - 1 / 2| := by rw [hβim, abs_sub_comm]
  have hnormγ : ‖D.γ₀‖ = ‖gammaOf ρ₀‖ := by rw [hD]
  rw [himγ, hnormγ] at hF
  have hG0 : 0 ≤ expTail Φ (1 / 2 + 3 / 2 * ((2 * k : ℕ) : ℝ)) 0 := expTail_nonneg _ _ _
  have hpow : ((2 : ℝ) ^ (2 * k)) ^ 2 = 16 ^ k := by
    rw [← pow_mul, show 2 * k * 2 = 4 * k by ring, pow_mul]; norm_num
  rw [hpow] at hF
  -- assemble
  have hall := hX.trans hF
  set Pre := C * 16 ^ k * (1 + 1 / |ρ₀.re - 1 / 2|) ^ 2 * (1 + ‖gammaOf ρ₀‖) ^ 2 *
    Real.exp (a / 2) with hPre
  have hPre0 : 0 ≤ Pre := by positivity
  have hall2 : (ρ₀.re * (1 - ρ₀.re) / 128 * (E * mv)) * (ρ₀.re * (1 - ρ₀.re) / 128 * (E * mv)) ≤
      Pre * ((80 * Mθ * Real.exp π + 1) * Real.exp ((1 / 2 + 3 * (k : ℝ) + 9 / 2) *
        (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8)))) *
        expTail Φ (1 / 2 + 3 / 2 * ((2 * k : ℕ) : ℝ)) 0 := by
    refine hall.trans ?_
    rw [hPre]
    gcongr
  have hEE : E * E = Real.exp (-(π * ρ₀.im / 2)) := by
    rw [hE, ← Real.exp_add]; ring_nf
  calc (ρ₀.re * (1 - ρ₀.re)) ^ 2 * Real.exp (-(π * ρ₀.im / 2)) * mv ^ 2
      = 128 ^ 2 * ((ρ₀.re * (1 - ρ₀.re) / 128 * (E * mv)) *
          (ρ₀.re * (1 - ρ₀.re) / 128 * (E * mv))) := by rw [← hEE]; ring
    _ ≤ 128 ^ 2 * (Pre * ((80 * Mθ * Real.exp π + 1) * Real.exp ((1 / 2 + 3 * (k : ℝ) + 9 / 2) *
          (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8)))) *
          expTail Φ (1 / 2 + 3 / 2 * ((2 * k : ℕ) : ℝ)) 0) := by gcongr
    _ = _ := by rw [hPre]; ring

theorem expTail_riemannPhiKernel_pos (c : ℝ) : 0 < expTail Φ c 0 := by
  by_contra h
  push Not at h
  have h0 : expTail Φ c 0 = 0 := le_antisymm h (expTail_nonneg _ _ _)
  have hint := superExpDecay_riemannPhiKernel.integrable_tail c 0
  have hnn : 0 ≤ᵐ[volume] ({u : ℝ | (0 : ℝ) ≤ |u|}.indicator
      (fun u => ‖Φ u‖ * Real.exp (c * |u|))) :=
    Eventually.of_forall fun u => by simp only [indicator]; split_ifs <;> positivity
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp h0
  have hΦ0 : Φ =ᵐ[volume] 0 := by
    filter_upwards [hae] with u hu
    simp only [indicator, mem_setOf_eq, abs_nonneg, if_true, Pi.zero_apply] at hu
    have := (mul_eq_zero.mp hu).resolve_right (Real.exp_pos _).ne'
    simpa using this
  have hzero : riemannXiHat (-(3 / 2 * I)) = 0 := by
    unfold riemannXiHat paperFT
    apply integral_eq_zero_of_ae
    filter_upwards [hΦ0] with u hu
    simp only [Pi.zero_apply] at hu ⊢
    rw [hu, zero_mul]
  exact riemannXiHat_ne_zero hzero

/-- **The Nyquist horizon.** Under the hypotheses of `hodgeIndex_excludes_separated_zero`,
`π e^{2a - 3/4} ≤ (π/2) t₀ + E`, where
`E = 2C log(t₀+1)(16(N+1)/d + 1) + (3k+5)(a-3/8) + a/2`
`  + log(9K 16^k (1 + 1/|β₀-½|)² (1+|γ₀|)² G_Φ(2k) / (β₀(1-β₀))²)`.
So the level-`a` Hodge index excludes every separated off-line zero with
`t₀ < 2e^{2a-3/4} - 2E/π`. `E` is polylogarithmic in `t₀` and linear in `a` for fixed `k`,
`N`, `d`. -/
theorem hodgeIndex_nyquist_horizon :
    ∃ K : ℝ, 0 < K ∧ ∀ {a : ℝ}, 1 ≤ a → HodgeIndexAtLevel zetaZeroConfig a →
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → 1 / 2 < ρ₀.re → 8 ≤ ρ₀.im →
      ∀ {d : ℝ}, 0 < d → (∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → d ≤ ‖ρ - ρ₀‖) →
      ∀ {k : ℕ} {v : ℂ → ℂ}, AnalyticAt ℂ v ρ₀ → v ρ₀ ≠ 0 →
        (∀ᶠ s in 𝓝 ρ₀, riemannZeta s = (s - ρ₀) ^ k * v s) →
        1 / 2 + 3 * (k : ℝ) + 11 / 2 ≤ 2 * π * Real.exp (2 * (a - 3 / 8)) →
        π * Real.exp (2 * (a - 3 / 8)) ≤ π * ρ₀.im / 2 +
          (2 * (logDerivZetaConstant * Real.log (ρ₀.im + 1) *
            (16 * ((windowOrdinates ρ₀.im).card + 1) / d + 1)) +
          (1 / 2 + 3 * (k : ℝ) + 9 / 2) * (a - 3 / 8) + a / 2 +
          Real.log (9 * K * 16 ^ k * (1 + 1 / |ρ₀.re - 1 / 2|) ^ 2 * (1 + ‖gammaOf ρ₀‖) ^ 2 *
            expTail Φ (1 / 2 + 3 / 2 * ((2 * k : ℕ) : ℝ)) 0 / (ρ₀.re * (1 - ρ₀.re)) ^ 2)) := by
  obtain ⟨K, hK, hexcl⟩ := hodgeIndex_excludes_separated_zero
  refine ⟨K, hK, fun {a} ha hH {ρ₀} hρ₀ hβ ht {d} hd hsep {k v} hv hv0 hloc hlam => ?_⟩
  have h := hexcl ha hH hρ₀ hβ ht hd hsep hv hv0 hloc hlam
  have hnt : IsNontrivialZero ρ₀ := hρ₀
  have hq : 0 < ρ₀.re * (1 - ρ₀.re) := mul_pos hnt.2.1 (by linarith [hnt.2.2])
  have hG := expTail_riemannPhiKernel_pos (1 / 2 + 3 / 2 * ((2 * k : ℕ) : ℝ))
  set Q := logDerivZetaConstant * Real.log (ρ₀.im + 1) *
    (16 * ((windowOrdinates ρ₀.im).card + 1) / d + 1) with hQ
  set G := expTail Φ (1 / 2 + 3 / 2 * ((2 * k : ℕ) : ℝ)) 0 with hGdef
  set B := 16 ^ k * (1 + 1 / |ρ₀.re - 1 / 2|) ^ 2 * (1 + ‖gammaOf ρ₀‖) ^ 2 with hB
  have hB0 : 0 < B := by positivity
  set Y := (1 / 2 + 3 * (k : ℝ) + 9 / 2) * (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8)) with hY
  -- rewrite both sides as exponentials
  have hL : (ρ₀.re * (1 - ρ₀.re)) ^ 2 * Real.exp (-(π * ρ₀.im / 2)) *
      ((1 / 3) * Real.exp (-Q)) ^ 2 =
      Real.exp (Real.log ((ρ₀.re * (1 - ρ₀.re)) ^ 2 / 9) - π * ρ₀.im / 2 - 2 * Q) := by
    rw [show Real.log ((ρ₀.re * (1 - ρ₀.re)) ^ 2 / 9) - π * ρ₀.im / 2 - 2 * Q =
      Real.log ((ρ₀.re * (1 - ρ₀.re)) ^ 2 / 9) + (-(π * ρ₀.im / 2)) + (-Q) + (-Q) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by positivity)]
    ring
  have hR : K * 16 ^ k * (1 + 1 / |ρ₀.re - 1 / 2|) ^ 2 * (1 + ‖gammaOf ρ₀‖) ^ 2 *
      Real.exp (a / 2) * G * Real.exp Y = Real.exp (Real.log (K * B * G) + a / 2 + Y) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity), hB]; ring
  rw [hL, hR] at h
  have hlog := Real.exp_le_exp.mp h
  have hsplit : Real.log (9 * K * B * G / (ρ₀.re * (1 - ρ₀.re)) ^ 2) =
      Real.log (K * B * G) - Real.log ((ρ₀.re * (1 - ρ₀.re)) ^ 2 / 9) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp
  have hgoal : Real.log (9 * K * 16 ^ k * (1 + 1 / |ρ₀.re - 1 / 2|) ^ 2 * (1 + ‖gammaOf ρ₀‖) ^ 2 *
      G / (ρ₀.re * (1 - ρ₀.re)) ^ 2) = Real.log (9 * K * B * G / (ρ₀.re * (1 - ρ₀.re)) ^ 2) := by
    rw [hB]; congr 1; ring
  rw [hgoal, hsplit]
  rw [hY] at hlog
  linarith

end

end RHTower
