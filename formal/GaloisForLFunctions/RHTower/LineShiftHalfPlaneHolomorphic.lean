import GaloisForLFunctions.RHTower.HerglotzWeilPositiveBridge

/-!
# Two-line residue identities for functions holomorphic on a half plane

The corpus two-line identity (`WeilLineIntegral.two_line_simple_pole`) and the critical-line shift
(`AtomDomination.integral_line_shift_critical`) assume entire integrands.  The rectangle residue
theorem needs holomorphy only on the rectangle, so both hold for functions holomorphic on a half
plane `Re s > a₀` containing the strip (`two_line_simple_pole_on`, `integral_line_shift_critical_on`).
This admits multipliers such as `(s + ½)^θ`.
-/

open Complex MeasureTheory Filter Topology Set
open Zeta23 Zeta23.WeilEF

namespace RHTower.LineShiftOn

noncomputable section

theorem differentiableAt_of_on {H : ℂ → ℂ} {a₀ : ℝ} (hH : DifferentiableOn ℂ H {s | a₀ < s.re})
    {s : ℂ} (hs : a₀ < s.re) : DifferentiableAt ℂ H s :=
  (hH s hs).differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

theorem integrable_line_div_on {H : ℂ → ℂ} {a₀ : ℝ} (hH : DifferentiableOn ℂ H {s | a₀ < s.re})
    {a b C : ℝ} (ha : a₀ < a)
    (hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → ‖H (σ + t * I)‖ ≤ C / (1 + t ^ 2)) {σ : ℝ} (h1 : a ≤ σ)
    (h2 : σ ≤ b) {p : ℂ} (hne : σ ≠ p.re) :
    Integrable (fun t : ℝ => H (σ + t * I) / (σ + t * I - p)) := by
  have hC0 : 0 ≤ C := by
    have := hC σ 0 h1 h2
    simp at this
    exact (norm_nonneg _).trans this
  have hd : 0 < |σ - p.re| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hne' : ∀ t : ℝ, (σ : ℂ) + t * I - p ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    exact hne (by linarith)
  have hcont : Continuous (fun t : ℝ => H (σ + t * I) / (σ + t * I - p)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hl : ContinuousAt (fun t : ℝ => (σ : ℂ) + t * I) t := by fun_prop
    have hre : a₀ < ((σ : ℂ) + t * I).re := by simp; linarith
    have hHc : ContinuousAt (fun t : ℝ => H ((σ : ℂ) + t * I)) t :=
      ContinuousAt.comp (g := H) (f := fun t : ℝ => (σ : ℂ) + t * I)
        (differentiableAt_of_on hH hre).continuousAt hl
    exact hHc.div (hl.sub continuousAt_const) (hne' t)
  have hdom : Integrable (fun t : ℝ => C / |σ - p.re| * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_div]
  have hden : |σ - p.re| ≤ ‖(σ : ℂ) + t * I - p‖ := by
    have := Complex.abs_re_le_norm ((σ : ℂ) + t * I - p)
    simpa using this
  rw [div_le_iff₀ (lt_of_lt_of_le hd hden)]
  calc ‖H (σ + t * I)‖ ≤ C / (1 + t ^ 2) := hC σ t h1 h2
    _ = C / |σ - p.re| * (1 + t ^ 2)⁻¹ * |σ - p.re| := by field_simp
    _ ≤ C / |σ - p.re| * (1 + t ^ 2)⁻¹ * ‖(σ : ℂ) + t * I - p‖ := by gcongr

/-- **Two vertical lines and one simple pole**, for `H` holomorphic on `Re s > a₀`, `a₀ < a`. -/
theorem two_line_simple_pole_on {H : ℂ → ℂ} {a₀ : ℝ} (hH : DifferentiableOn ℂ H {s | a₀ < s.re})
    {a b C : ℝ} (ha : a₀ < a)
    (hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → ‖H (σ + t * I)‖ ≤ C / (1 + t ^ 2)) {p : ℂ}
    (hp1 : a < p.re) (hp2 : p.re < b) :
    (∫ t : ℝ, H (b + t * I) / (b + t * I - p)) - (∫ t : ℝ, H (a + t * I) / (a + t * I - p)) =
      2 * Real.pi * H p := by
  set f : ℂ → ℂ := fun s => H s / (s - p) with hf
  have hab : a ≤ b := by linarith
  have hC0 : 0 ≤ C := by
    have := hC a 0 le_rfl hab
    simp at this
    exact (norm_nonneg _).trans this
  have hres : ∀ R : ℝ, |p.im| < R →
      RectangleIntegral' f ((a : ℂ) + (-R : ℝ) * I) ((b : ℂ) + (R : ℝ) * I) = H p := by
    intro R hR
    have hRp : 0 < R := lt_of_le_of_lt (abs_nonneg _) hR
    refine ResidueTheoremOnRectangleWithSimplePole' (p := p) (by simp; linarith) (by simp; linarith)
      ?_ ?_ ?_
    · rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
        add_zero, add_im, mul_im, zero_add]
      rw [Set.uIoo_of_le hab, Set.uIoo_of_le (by linarith)]
      exact ⟨⟨hp1, hp2⟩, ⟨by linarith [neg_abs_le p.im], by linarith [le_abs_self p.im]⟩⟩
    · intro s hs
      have hsre : a₀ < s.re := by
        have hrect := hs.1
        rw [Rectangle, Complex.mem_reProdIm] at hrect
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
          add_zero] at hrect
        rw [Set.uIcc_of_le hab] at hrect
        linarith [hrect.1.1]
      exact ((differentiableAt_of_on hH hsre).div (differentiableAt_id.sub_const p)
        (sub_ne_zero.mpr hs.2)).differentiableWithinAt
    · have hO : (fun s => H s - H p) =O[𝓝[≠] p] (fun s => s - p) :=
        ((differentiableAt_of_on hH (by linarith)).hasDerivAt.isBigO_sub).mono nhdsWithin_le_nhds
      have h2 := hO.mul (Asymptotics.isBigO_refl (fun s : ℂ => (s - p)⁻¹) (𝓝[≠] p))
      refine (h2.congr' ?_ ?_)
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [hf, Pi.sub_apply]
        ring
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact mul_inv_cancel₀ (sub_ne_zero.mpr hs)
  have hline : ∀ σ : ℝ, a ≤ σ → σ ≤ b → σ ≠ p.re →
      Integrable (fun t : ℝ => f (σ + t * I)) := fun σ h1 h2 hne =>
    integrable_line_div_on hH ha hC h1 h2 hne
  have hib := hline b hab le_rfl hp2.ne'
  have hia := hline a le_rfl hab hp1.ne
  have hbound : ∀ R : ℝ, |p.im| + 1 ≤ |R| → ∀ x ∈ Set.uIcc a b,
      ‖f (x + R * I)‖ ≤ C / (1 + R ^ 2) := by
    intro R hR x hx
    rw [Set.uIcc_of_le hab] at hx
    simp only [hf, norm_div]
    have hden : 1 ≤ ‖(x : ℂ) + R * I - p‖ := by
      have := Complex.abs_im_le_norm ((x : ℂ) + R * I - p)
      simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add] at this
      have h' : |p.im| + 1 ≤ |R - p.im| + |p.im| := by
        have := abs_sub_abs_le_abs_sub R p.im
        linarith
      linarith
    calc ‖H (x + R * I)‖ / ‖(x : ℂ) + R * I - p‖ ≤ ‖H (x + R * I)‖ / 1 :=
          div_le_div_of_nonneg_left (norm_nonneg _) one_pos hden
      _ ≤ C / (1 + R ^ 2) := by rw [div_one]; exact hC x R hx.1 hx.2
  have hlim : Tendsto (fun R : ℝ => C / (1 + R ^ 2) * |b - a|) atTop (𝓝 0) := by
    have : Tendsto (fun R : ℝ => C / (1 + R ^ 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1
        (tendsto_pow_atTop (by norm_num)))
    simpa using this.mul_const |b - a|
  have htop : Tendsto (fun R : ℝ => HIntegral f a b R) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (|p.im| + 1)] with R hR
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hbound R (by rw [abs_of_nonneg (show (0 : ℝ) ≤ R by linarith [abs_nonneg p.im])]; exact hR) x
        (Set.uIoc_subset_uIcc hx)
  have hbot : Tendsto (fun R : ℝ => HIntegral f a b (-R)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (|p.im| + 1)] with R hR
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    have h := hbound (-R)
      (by rw [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ R by linarith [abs_nonneg p.im])]; exact hR)
      x (Set.uIoc_subset_uIcc hx)
    simpa using h
  have hvb : Tendsto (fun R : ℝ => ∫ t in (-R)..R, f (b + t * I)) atTop
      (𝓝 (∫ t : ℝ, f (b + t * I))) :=
    intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  have hva : Tendsto (fun R : ℝ => ∫ t in (-R)..R, f (a + t * I)) atTop
      (𝓝 (∫ t : ℝ, f (a + t * I))) :=
    intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  have hdec : ∀ R : ℝ, RectangleIntegral' f ((a : ℂ) + (-R : ℝ) * I) ((b : ℂ) + (R : ℝ) * I) =
      (1 / (2 * Real.pi * I)) * (HIntegral f a b (-R) - HIntegral f a b R +
        I * (∫ t in (-R)..R, f (b + t * I)) - I * (∫ t in (-R)..R, f (a + t * I))) := by
    intro R
    simp only [RectangleIntegral', RectangleIntegral, VIntegral, smul_eq_mul]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      add_zero, add_im, mul_im, zero_add]
  have hlimit : Tendsto (fun R : ℝ => RectangleIntegral' f ((a : ℂ) + (-R : ℝ) * I)
      ((b : ℂ) + (R : ℝ) * I)) atTop
      (𝓝 ((1 / (2 * Real.pi * I)) * (0 - 0 + I * (∫ t : ℝ, f (b + t * I)) -
        I * (∫ t : ℝ, f (a + t * I))))) := by
    simp_rw [hdec]
    exact (((hbot.sub htop).add (hvb.const_mul I)).sub (hva.const_mul I)).const_mul _
  have hconst : Tendsto (fun R : ℝ => RectangleIntegral' f ((a : ℂ) + (-R : ℝ) * I)
      ((b : ℂ) + (R : ℝ) * I)) atTop (𝓝 (H p)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop |p.im|] with R hR
    exact (hres R hR).symm
  have heq := tendsto_nhds_unique hconst hlimit
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e1 : (∫ t : ℝ, f (b + t * I)) = ∫ t : ℝ, H (b + t * I) / (b + t * I - p) := rfl
  have e2 : (∫ t : ℝ, f (a + t * I)) = ∫ t : ℝ, H (a + t * I) / (a + t * I - p) := rfl
  rw [← e1, ← e2, heq]
  have hk : (2 * Real.pi : ℂ) * (1 / (2 * Real.pi * I)) * I = 1 := by field_simp
  linear_combination (-(∫ t : ℝ, f (b + t * I)) + ∫ t : ℝ, f (a + t * I)) * hk

/-- **Moving a line integral to the critical line**, for a multiplier `q` holomorphic on
`Re s > a₀` (`a₀ < ½`) with `|q(σ + it)| ≤ A(1 + |t|)` on `½ ≤ σ ≤ b`. -/
theorem integral_line_shift_critical_on {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {D : ℝ}
    (hD : ∀ σ t : ℝ, -1 ≤ σ → σ ≤ 2 → ‖Hfn k (σ + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2)
    {q : ℂ → ℂ} {a₀ : ℝ} (ha₀ : a₀ < 1 / 2) (hq : DifferentiableOn ℂ q {s | a₀ < s.re})
    {b A : ℝ} (hb1 : 3 / 4 < b) (hb2 : b ≤ 3 / 2) (hA : 0 ≤ A)
    (hqb : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ b → ‖q (σ + t * I)‖ ≤ A * (1 + |t|)) :
    (∫ t : ℝ, (Hfn k (b + t * I) + Hfn k (1 - b - t * I)) * q (b + t * I)) =
      ∫ t : ℝ, (Hfn k ((1 / 2 : ℝ) + t * I) + Hfn k ((1 / 2 : ℝ) - t * I)) *
        q ((1 / 2 : ℝ) + t * I) := by
  set E : ℂ → ℂ := fun s => (Hfn k s + Hfn k (1 - s)) * q s * (s - 3 / 4) with hE
  have hHd := WeilLineIntegral.differentiable_Hfn hk hkc
  have hEd : DifferentiableOn ℂ E {s | a₀ < s.re} := by
    intro s hs
    exact ((((hHd s).add ((hHd (1 - s)).comp s ((differentiableAt_const 1).sub
      differentiableAt_id))).mul (differentiableAt_of_on hq hs)).mul
      (differentiableAt_id.sub_const _)).differentiableWithinAt
  have hD0 : 0 ≤ D := by
    have := hD 0 0 (by norm_num) (by norm_num)
    simp at this
    exact (norm_nonneg _).trans this
  have hEb : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ b → ‖E (σ + t * I)‖ ≤ 4 * A * D / (1 + t ^ 2) := by
    intro σ t h1 h2
    have e : (1 : ℂ) - (σ + t * I) = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    have hA' := hD σ t (by linarith) (by linarith)
    have hB := hD (1 - σ) (-t) (by linarith) (by linarith)
    rw [neg_sq] at hB
    have hlin : ‖(σ : ℂ) + t * I - 3 / 4‖ ≤ 1 + |t| := by
      have e2 : (σ : ℂ) + t * I - 3 / 4 = ((σ - 3 / 4 : ℝ) : ℂ) + t * I := by push_cast; ring
      rw [e2]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have : |σ - 3 / 4| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have hq' := hqb σ t h1 h2
    have hsq : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
    simp only [hE]
    rw [norm_mul, norm_mul, e]
    calc ‖Hfn k (σ + t * I) + Hfn k (((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ *
          ‖q (σ + t * I)‖ * ‖(σ : ℂ) + t * I - 3 / 4‖
        ≤ (D / (1 + t ^ 2) ^ 2 + D / (1 + t ^ 2) ^ 2) * (A * (1 + |t|)) * (1 + |t|) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hA' hB)
      _ = 2 * A * D * (1 + |t|) ^ 2 / (1 + t ^ 2) ^ 2 := by ring
      _ ≤ 2 * A * D * (2 * (1 + t ^ 2)) / (1 + t ^ 2) ^ 2 := by gcongr
      _ = 4 * A * D / (1 + t ^ 2) := by field_simp; ring
  have h := two_line_simple_pole_on hEd (by norm_num; linarith) hEb (p := 3 / 4) (by norm_num)
    (by norm_num; linarith)
  have hE0 : E (3 / 4) = 0 := by simp [hE]
  rw [hE0, mul_zero, sub_eq_zero] at h
  have hR : ∀ t : ℝ, E (b + t * I) / (b + t * I - 3 / 4) =
      (Hfn k (b + t * I) + Hfn k (1 - b - t * I)) * q (b + t * I) := by
    intro t
    have hne : (b : ℂ) + t * I - 3 / 4 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    simp only [hE]
    rw [mul_div_cancel_right₀ _ hne, sub_add_eq_sub_sub]
  have hL : ∀ t : ℝ, E (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I - 3 / 4) =
      (Hfn k ((1 / 2 : ℝ) + t * I) + Hfn k ((1 / 2 : ℝ) - t * I)) * q ((1 / 2 : ℝ) + t * I) := by
    intro t
    have hne : ((1 / 2 : ℝ) : ℂ) + t * I - 3 / 4 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      norm_num at this
    simp only [hE]
    rw [mul_div_cancel_right₀ _ hne]
    congr 3
    push_cast
    ring
  simp_rw [hR, hL] at h
  exact h

end

end RHTower.LineShiftOn
