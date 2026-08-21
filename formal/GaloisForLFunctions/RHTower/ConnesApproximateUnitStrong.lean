import GaloisForLFunctions.RHTower.ConnesSobolevTranslationOperator

/-!
# The smeared translation operators `V(f)` and Connes' approximate unit

Appendix I (5) and Lemma 4 of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

`V(f) = ∫ f(v) V(v) dv` makes sense on `L²_δ(ℝ)` as soon as `∫ |f(v)| ρ_δ(v)^{1/2} dv < ∞`,
because `‖V(v)‖ ≤ (2^{δ/2}ρ_δ(v))^{1/2}` and `v ↦ V(v)ξ` is norm continuous.  For a rescaled
family `f_n(v) = n f(nv)` with `∫ f = 1` the weight only shrinks, `ρ_δ(v/n) ≤ ρ_δ(v)`, so the
same integrable profile dominates every `n`, and dominated convergence against the continuity of
translation gives `V(f_n) → 1` strongly.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The operator-norm profile of the translation family. -/
def connesTranslateBound (δ v : ℝ) : ℝ :=
  Real.sqrt (2 ^ (δ / 2) * connesSobolevWeight δ v)

theorem connesTranslateBound_nonneg (δ v : ℝ) : 0 ≤ connesTranslateBound δ v :=
  Real.sqrt_nonneg _

theorem one_le_connesTranslateBound {δ : ℝ} (hδ : 0 ≤ δ) (v : ℝ) :
    1 ≤ connesTranslateBound δ v := by
  have h1 : (1 : ℝ) ≤ 2 ^ (δ / 2) := Real.one_le_rpow (by norm_num) (by linarith)
  have h2 : (1 : ℝ) ≤ connesSobolevWeight δ v := by
    unfold connesSobolevWeight
    refine Real.one_le_rpow (by nlinarith [sq_nonneg v]) (by linarith)
  have : (1 : ℝ) ≤ 2 ^ (δ / 2) * connesSobolevWeight δ v := by nlinarith
  rw [connesTranslateBound, show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt this

theorem norm_connesTranslate_le' {δ : ℝ} (hδ : 0 ≤ δ) (v : ℝ)
    (ξ : Lp ℂ 2 (connesSobolevMeasure δ)) :
    ‖connesTranslate hδ v ξ‖ ≤ connesTranslateBound δ v * ‖ξ‖ :=
  norm_connesTranslate_le hδ v ξ

theorem connes_integrable_of_weighted {δ : ℝ} (hδ : 0 ≤ δ) {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f volume)
    (hf : Integrable (fun v => ‖f v‖ * connesTranslateBound δ v) volume) :
    Integrable f volume := by
  refine hf.mono' hfm ?_
  filter_upwards with v
  nlinarith [norm_nonneg (f v), one_le_connesTranslateBound hδ v]

theorem connes_integrable_smul_translate {δ : ℝ} (hδ : 0 ≤ δ) {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f volume)
    (hf : Integrable (fun v => ‖f v‖ * connesTranslateBound δ v) volume)
    (ξ : Lp ℂ 2 (connesSobolevMeasure δ)) :
    Integrable (fun v => f v • connesTranslate hδ v ξ) volume := by
  refine Integrable.mono (hf.smul ‖ξ‖) ?_ ?_
  · exact hfm.smul (continuous_connesTranslate hδ ξ).aestronglyMeasurable
  · filter_upwards with v
    have hb0 : (0 : ℝ) ≤ ‖ξ‖ * (‖f v‖ * connesTranslateBound δ v) := by
      have := connesTranslateBound_nonneg δ v
      positivity
    simp only [norm_smul, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg hb0]
    nlinarith [norm_connesTranslate_le' hδ v ξ, norm_nonneg (f v), norm_nonneg ξ,
      connesTranslateBound_nonneg δ v]

/-- **Appendix I (5).**  The smeared translation `V(f) = ∫ f(v) V(v) dv`. -/
def connesV {δ : ℝ} (hδ : 0 ≤ δ) (f : ℝ → ℂ) (ξ : Lp ℂ 2 (connesSobolevMeasure δ)) :
    Lp ℂ 2 (connesSobolevMeasure δ) :=
  ∫ v, f v • connesTranslate hδ v ξ

/-- The defect of `V(f)` from the identity is the smeared defect of the translations. -/
theorem connesV_sub {δ : ℝ} (hδ : 0 ≤ δ) {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f volume)
    (hf : Integrable (fun v => ‖f v‖ * connesTranslateBound δ v) volume)
    (hf1 : ∫ v, f v = 1) (ξ : Lp ℂ 2 (connesSobolevMeasure δ)) :
    connesV hδ f ξ - ξ = ∫ v, f v • (connesTranslate hδ v ξ - ξ) := by
  have hfint : Integrable f volume := connes_integrable_of_weighted hδ hfm hf
  have h1 : Integrable (fun v => f v • connesTranslate hδ v ξ) volume :=
    connes_integrable_smul_translate hδ hfm hf ξ
  have h2 : Integrable (fun v => f v • ξ) volume := hfint.smul_const ξ
  have hconst : (∫ v, f v • ξ) = ξ := by
    rw [integral_smul_const, hf1, one_smul]
  have hsplit : (fun v => f v • (connesTranslate hδ v ξ - ξ))
      = fun v => f v • connesTranslate hδ v ξ - f v • ξ := by
    funext v
    rw [smul_sub]
  rw [connesV, hsplit, integral_sub h1 h2, hconst]

theorem norm_connesV_sub_le {δ : ℝ} (hδ : 0 ≤ δ) {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f volume)
    (hf : Integrable (fun v => ‖f v‖ * connesTranslateBound δ v) volume)
    (hf1 : ∫ v, f v = 1) (ξ : Lp ℂ 2 (connesSobolevMeasure δ)) :
    ‖connesV hδ f ξ - ξ‖ ≤ ∫ v, ‖f v‖ * ‖connesTranslate hδ v ξ - ξ‖ := by
  rw [connesV_sub hδ hfm hf hf1 ξ]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  rw [norm_smul]

/-! ### The rescaled approximate unit -/

theorem continuous_connesTranslateBound (δ : ℝ) : Continuous (connesTranslateBound δ) :=
  Real.continuous_sqrt.comp (continuous_const.mul (continuous_connesSobolevWeight δ))

/-- The rescaled family `f_a(v) = a f(a v)` of Appendix I (6). -/
def connesDilate (f : ℝ → ℂ) (a : ℝ) : ℝ → ℂ := fun v => (a : ℂ) * f (a * v)

theorem norm_connesDilate {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (v : ℝ) :
    ‖connesDilate f a v‖ = a * ‖f (a * v)‖ := by
  simp only [connesDilate, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]

theorem integral_connesDilate {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) :
    ∫ v, connesDilate f a v = ∫ v, f v := by
  have hcv := Measure.integral_comp_mul_left (fun w : ℝ => f w) a
  simp only [connesDilate]
  rw [integral_const_mul, hcv, abs_of_pos (inv_pos.mpr ha), Complex.real_smul,
    ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ha.ne']
  simp

theorem connesTranslateBound_mono {δ : ℝ} (hδ : 0 ≤ δ) {u v : ℝ} (h : |u| ≤ |v|) :
    connesTranslateBound δ u ≤ connesTranslateBound δ v := by
  have hsq : u ^ 2 ≤ v ^ 2 := by
    have h1 : |u| ^ 2 ≤ |v| ^ 2 := by nlinarith [abs_nonneg u, abs_nonneg v]
    rwa [sq_abs, sq_abs] at h1
  have hpow : (0 : ℝ) < 2 ^ (δ / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hw : connesSobolevWeight δ u ≤ connesSobolevWeight δ v := by
    unfold connesSobolevWeight
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hw hpow.le)

theorem connes_integrable_dilate {δ : ℝ} (hδ : 0 ≤ δ) {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f volume)
    (hf : Integrable (fun v => ‖f v‖ * connesTranslateBound δ v) volume)
    {a : ℝ} (ha : 1 ≤ a) :
    Integrable (fun v => ‖connesDilate f a v‖ * connesTranslateBound δ v) volume := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  set g : ℝ → ℝ := fun w => a * ‖f w‖ * connesTranslateBound δ (a⁻¹ * w) with hg
  have hgint : Integrable g volume := by
    refine Integrable.mono (hf.const_mul a) ?_ ?_
    · refine AEStronglyMeasurable.mul (hfm.norm.const_mul a) ?_
      exact ((continuous_connesTranslateBound δ).comp
        (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards with w
      have hb : |a⁻¹ * w| ≤ |w| := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr ha0)]
        have h1 : a⁻¹ ≤ 1 := by
          rw [inv_le_one_iff₀]
          exact Or.inr ha
        nlinarith [abs_nonneg w]
      have hmono := connesTranslateBound_mono hδ hb
      have hnn1 : 0 ≤ a * ‖f w‖ := by positivity
      have hnn2 : 0 ≤ connesTranslateBound δ (a⁻¹ * w) := connesTranslateBound_nonneg _ _
      have hnn3 : 0 ≤ connesTranslateBound δ w := connesTranslateBound_nonneg _ _
      rw [hg, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ a * ‖f w‖ * connesTranslateBound δ (a⁻¹ * w)),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ a * (‖f w‖ * connesTranslateBound δ w))]
      nlinarith
  have hcomp : Integrable (fun v => g (a * v)) volume :=
    (integrable_comp_mul_left_iff g ha0.ne').mpr hgint
  refine hcomp.congr ?_
  filter_upwards with v
  rw [hg]
  simp only
  rw [norm_connesDilate ha0, ← mul_assoc]
  congr 2
  rw [inv_mul_cancel₀ ha0.ne', one_mul]

theorem connes_quasiMeasurePreserving_mul_left {a : ℝ} (ha : a ≠ 0) :
    Measure.QuasiMeasurePreserving (fun v : ℝ => a * v) volume volume := by
  refine ⟨measurable_const_mul a, ?_⟩
  rw [Real.map_volume_mul_left ha]
  exact Measure.absolutelyContinuous_of_le_smul (c := ENNReal.ofReal |a⁻¹|) le_rfl

theorem connes_aestronglyMeasurable_dilate {f : ℝ → ℂ} (hfm : AEStronglyMeasurable f volume)
    {a : ℝ} (ha : a ≠ 0) : AEStronglyMeasurable (connesDilate f a) volume := by
  show AEStronglyMeasurable (fun v : ℝ => (a : ℂ) * f (a * v)) volume
  exact
    (hfm.comp_quasiMeasurePreserving (connes_quasiMeasurePreserving_mul_left ha)).const_mul _

/-- The defect of the dilated smeared translation, after the change of variables `v = w/a`. -/
theorem connes_norm_connesV_dilate_le {δ : ℝ} (hδ : 0 ≤ δ) {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f volume)
    (hf : Integrable (fun v => ‖f v‖ * connesTranslateBound δ v) volume)
    (hf1 : ∫ v, f v = 1) (ξ : Lp ℂ 2 (connesSobolevMeasure δ)) {a : ℝ} (ha : 1 ≤ a) :
    ‖connesV hδ (connesDilate f a) ξ - ξ‖
      ≤ ∫ w, ‖f w‖ * ‖connesTranslate hδ (a⁻¹ * w) ξ - ξ‖ := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have h1 := norm_connesV_sub_le hδ (connes_aestronglyMeasurable_dilate hfm ha0.ne')
    (connes_integrable_dilate hδ hfm hf ha)
    (by rw [integral_connesDilate ha0, hf1]) ξ
  refine le_trans h1 (le_of_eq ?_)
  have hpt : ∀ v : ℝ,
      ‖connesDilate f a v‖ * ‖connesTranslate hδ v ξ - ξ‖
        = a * ((fun w : ℝ => ‖f w‖ * ‖connesTranslate hδ (a⁻¹ * w) ξ - ξ‖) (a * v)) := by
    intro v
    show ‖connesDilate f a v‖ * ‖connesTranslate hδ v ξ - ξ‖
      = a * (‖f (a * v)‖ * ‖connesTranslate hδ (a⁻¹ * (a * v)) ξ - ξ‖)
    rw [inv_mul_cancel_left₀ ha0.ne', norm_connesDilate ha0, mul_assoc]
  have hint : (∫ v, ‖connesDilate f a v‖ * ‖connesTranslate hδ v ξ - ξ‖)
      = ∫ v, a * ((fun w : ℝ => ‖f w‖ * ‖connesTranslate hδ (a⁻¹ * w) ξ - ξ‖) (a * v)) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hint, integral_const_mul,
    Measure.integral_comp_mul_left
      (fun w : ℝ => ‖f w‖ * ‖connesTranslate hδ (a⁻¹ * w) ξ - ξ‖) a,
    abs_of_pos (inv_pos.mpr ha0), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul]

/-- **Appendix I Lemma 4.**  The rescaled family `f_n(v) = n f(nv)` of an integrable profile with
unit mass gives an approximate unit: `V(f_n) → 1` strongly on `L²_δ(ℝ)`. -/
theorem connes_approxUnit_tendsto {δ : ℝ} (hδ : 0 ≤ δ) {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f volume)
    (hf : Integrable (fun v => ‖f v‖ * connesTranslateBound δ v) volume)
    (hf1 : ∫ v, f v = 1) (ξ : Lp ℂ 2 (connesSobolevMeasure δ)) :
    Tendsto (fun n : ℕ => connesV hδ (connesDilate f ((n : ℝ) + 1)) ξ) atTop (𝓝 ξ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hfint : Integrable f volume := connes_integrable_of_weighted hδ hfm hf
  set D : ℝ → ℝ := fun w => ‖ξ‖ * (‖f w‖ * connesTranslateBound δ w + ‖f w‖) with hD
  have hDint : Integrable D volume := (hf.add hfint.norm).const_mul ‖ξ‖
  set H : ℕ → ℝ → ℝ := fun n w =>
    ‖f w‖ * ‖connesTranslate hδ (((n : ℝ) + 1)⁻¹ * w) ξ - ξ‖ with hH
  have hcpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hHmeas : ∀ n, AEStronglyMeasurable (H n) volume := by
    intro n
    refine hfm.norm.mul ?_
    refine Continuous.aestronglyMeasurable ?_
    exact (((continuous_connesTranslate hδ ξ).comp
      (continuous_const.mul continuous_id)).sub continuous_const).norm
  have hHbound : ∀ n, ∀ᵐ w ∂(volume : Measure ℝ), ‖H n w‖ ≤ D w := by
    intro n
    filter_upwards with w
    have hcn := hcpos n
    have habs : |((n : ℝ) + 1)⁻¹ * w| ≤ |w| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hcn)]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        exact Or.inr (by linarith)
      nlinarith [abs_nonneg w]
    have hmono := connesTranslateBound_mono hδ habs
    have hnormle : ‖connesTranslate hδ (((n : ℝ) + 1)⁻¹ * w) ξ - ξ‖
        ≤ connesTranslateBound δ w * ‖ξ‖ + ‖ξ‖ := by
      refine le_trans (norm_sub_le _ _) ?_
      refine add_le_add ?_ (le_refl _)
      refine le_trans (norm_connesTranslate_le' hδ _ ξ) ?_
      exact mul_le_mul_of_nonneg_right hmono (norm_nonneg ξ)
    have hHnn : 0 ≤ H n w := by
      rw [hH]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hHnn, hH, hD]
    simp only
    nlinarith [norm_nonneg (f w), norm_nonneg ξ, connesTranslateBound_nonneg δ w]
  have hHlim : ∀ᵐ w ∂(volume : Measure ℝ), Tendsto (fun n : ℕ => H n w) atTop (𝓝 0) := by
    filter_upwards with w
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      exact h1.inv_tendsto_atTop
    have hcw : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * w) atTop (𝓝 0) := by
      have := hinv.mul_const w
      simpa using this
    have htr : Tendsto (fun n : ℕ => connesTranslate hδ (((n : ℝ) + 1)⁻¹ * w) ξ) atTop
        (𝓝 (connesTranslate hδ 0 ξ)) :=
      ((continuous_connesTranslate hδ ξ).tendsto 0).comp hcw
    rw [connesTranslate_zero] at htr
    have hnorm : Tendsto (fun n : ℕ =>
        ‖connesTranslate hδ (((n : ℝ) + 1)⁻¹ * w) ξ - ξ‖) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ => ξ) atTop (𝓝 ξ) := tendsto_const_nhds
      have h := (htr.sub hconst).norm
      simpa using h
    have := hnorm.const_mul ‖f w‖
    simpa [hH] using this
  have hlim : Tendsto (fun n : ℕ => ∫ w, H n w) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence D hHmeas hDint hHbound hHlim
    simpa using this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  exact connes_norm_connesV_dilate_le hδ hfm hf hf1 ξ hn1

end

end GaloisForLFunctions.RHTower