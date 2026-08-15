import Mathlib

/-!
# Power means of a unit-bounded density converge to its essential supremum

On a probability space the normalized moments of a function with values in the unit interval
increase with the exponent, by Hölder's inequality against the constant one, and converge to the
essential supremum.  The upper bound is the almost-everywhere bound by the essential supremum; the
lower bound comes from the positive mass of every level set strictly below it, whose weight
contributes a factor tending to one after taking the exponent-th root.
-/

open MeasureTheory Filter Real Topology

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section PowerMean

variable {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]

theorem isBoundedUnder_of_le_one {F : Ω → ℝ} (h1 : ∀ x, F x ≤ 1) :
    IsBoundedUnder (· ≤ ·) (ae ρ) F :=
  Filter.isBoundedUnder_of ⟨1, h1⟩

theorem isCoboundedUnder_of_nonneg {F : Ω → ℝ} (h0 : ∀ x, 0 ≤ F x) :
    IsCoboundedUnder (· ≤ ·) (ae ρ) F :=
  (Filter.isBoundedUnder_of (r := (· ≥ ·)) ⟨0, h0⟩).isCoboundedUnder_le

theorem ae_le_essSup_of_le_one {F : Ω → ℝ} (h1 : ∀ x, F x ≤ 1) :
    ∀ᵐ x ∂ρ, F x ≤ essSup F ρ :=
  ae_le_essSup (isBoundedUnder_of_le_one ρ h1)

theorem essSup_nonneg_of_nonneg {F : Ω → ℝ} (h0 : ∀ x, 0 ≤ F x) (h1 : ∀ x, F x ≤ 1) :
    0 ≤ essSup F ρ := by
  by_contra hcon
  have hlt : essSup F ρ < 0 := not_le.mp hcon
  have hfalse : ∀ᵐ _x ∂ρ, False := by
    filter_upwards [ae_le_essSup_of_le_one ρ h1] with x hx
    exact absurd (lt_of_le_of_lt hx hlt) (not_lt.mpr (h0 x))
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hfalse
  exact (IsProbabilityMeasure.ne_zero ρ) hfalse

theorem essSup_le_one_of_le_one {F : Ω → ℝ} (h0 : ∀ x, 0 ≤ F x) (h1 : ∀ x, F x ≤ 1) :
    essSup F ρ ≤ 1 :=
  essSup_le_of_ae_le 1 (Filter.Eventually.of_forall h1) (isCoboundedUnder_of_nonneg ρ h0)

theorem integrable_pow_of_unit {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) (r : ℕ) : Integrable (fun x => F x ^ r) ρ := by
  refine Integrable.of_bound (hF.pow_const r).aestronglyMeasurable 1 ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (pow_nonneg (h0 x) r)]
  exact pow_le_one₀ (h0 x) (h1 x)

theorem integral_pow_nonneg {F : Ω → ℝ} (h0 : ∀ x, 0 ≤ F x) (r : ℕ) :
    0 ≤ ∫ x, F x ^ r ∂ρ :=
  integral_nonneg fun x => pow_nonneg (h0 x) r

/-- **Upper moment bound.**  Every moment is dominated by the corresponding power of the essential
supremum. -/
theorem integral_pow_le_essSup_pow {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) (r : ℕ) :
    ∫ x, F x ^ r ∂ρ ≤ essSup F ρ ^ r := by
  have hmono : ∀ᵐ x ∂ρ, F x ^ r ≤ essSup F ρ ^ r := by
    filter_upwards [ae_le_essSup_of_le_one ρ h1] with x hx
    exact pow_le_pow_left₀ (h0 x) hx r
  calc ∫ x, F x ^ r ∂ρ ≤ ∫ _x, essSup F ρ ^ r ∂ρ :=
        integral_mono_ae (integrable_pow_of_unit ρ hF h0 h1 r) (integrable_const _) hmono
    _ = essSup F ρ ^ r := by simp

/-- **Lower moment bound.**  Every level set contributes its mass times the level to the power of
the exponent. -/
theorem measureReal_mul_pow_le_integral_pow {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) {c : ℝ} (hc : 0 ≤ c) (r : ℕ) :
    ρ.real {x | c ≤ F x} * c ^ r ≤ ∫ x, F x ^ r ∂ρ := by
  classical
  have hE : MeasurableSet {x | c ≤ F x} := measurableSet_le measurable_const hF
  have hpoint : ∀ x, c ^ r * Set.indicator {x | c ≤ F x} (1 : Ω → ℝ) x ≤ F x ^ r := by
    intro x
    by_cases hx : x ∈ {x | c ≤ F x}
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      exact pow_le_pow_left₀ hc hx r
    · rw [Set.indicator_of_notMem hx, mul_zero]
      exact pow_nonneg (h0 x) r
  have hindint : Integrable (Set.indicator {x | c ≤ F x} (1 : Ω → ℝ)) ρ := by
    rw [integrable_indicator_iff hE]
    exact integrableOn_const (by simp [measure_ne_top])
  have hmono := integral_mono (hindint.const_mul _) (integrable_pow_of_unit ρ hF h0 h1 r) hpoint
  rw [integral_const_mul, integral_indicator_one hE] at hmono
  rw [mul_comm]
  exact hmono

/-- Every level strictly below the essential supremum is reached with positive mass. -/
theorem measure_le_pos_of_lt_essSup {F : Ω → ℝ} (h0 : ∀ x, 0 ≤ F x) {c : ℝ}
    (hc : c < essSup F ρ) : 0 < ρ.real {x | c ≤ F x} := by
  have hne : ρ {x | c ≤ F x} ≠ 0 := by
    intro hzero
    have hae : F ≤ᵐ[ρ] fun _ => c := by
      rw [Filter.EventuallyLE, ae_iff]
      exact measure_mono_null (fun x hx => (not_le.mp hx).le) hzero
    exact absurd (essSup_le_of_ae_le c hae (isCoboundedUnder_of_nonneg ρ h0)) (not_le.mpr hc)
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

/-- A positive constant raised to the reciprocal of the exponent tends to one. -/
theorem tendsto_rpow_inv_const {p : ℝ} (hp : 0 < p) :
    Tendsto (fun r : ℕ => p ^ ((r : ℝ)⁻¹)) atTop (𝓝 1) := by
  have hcont : Tendsto (fun r : ℕ => Real.log p * (r : ℝ)⁻¹) atTop (𝓝 0) := by
    have := tendsto_const_div_atTop_nhds_zero_nat (Real.log p)
    simpa [div_eq_mul_inv] using this
  have := (Real.continuous_exp.tendsto 0).comp hcont
  simp only [Function.comp_def, Real.exp_zero] at this
  refine this.congr fun r => ?_
  rw [Real.rpow_def_of_pos hp]

/-- **Power means converge to the essential supremum.**  On a probability space the exponent-th
root of the exponent-th moment of a unit-bounded function tends to its essential supremum. -/
theorem tendsto_rpow_inv_integral_pow {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) :
    Tendsto (fun r : ℕ => (∫ x, F x ^ r ∂ρ) ^ ((r : ℝ)⁻¹)) atTop (𝓝 (essSup F ρ)) := by
  have hM0 : 0 ≤ essSup F ρ := essSup_nonneg_of_nonneg ρ h0 h1
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- lower half
    intro b hb
    rcases lt_or_ge b 0 with hbneg | hbpos
    · filter_upwards with r
      exact lt_of_lt_of_le hbneg (Real.rpow_nonneg (integral_pow_nonneg ρ h0 r) _)
    · set c : ℝ := (b + essSup F ρ) / 2 with hcdef
      have hbc : b < c := by rw [hcdef]; linarith
      have hcM : c < essSup F ρ := by rw [hcdef]; linarith
      have hc0 : 0 < c := lt_of_le_of_lt hbpos hbc
      set p : ℝ := ρ.real {x | c ≤ F x} with hpdef
      have hp0 : 0 < p := measure_le_pos_of_lt_essSup ρ h0 hcM
      have hlim : Tendsto (fun r : ℕ => p ^ ((r : ℝ)⁻¹) * c) atTop (𝓝 c) := by
        have := (tendsto_rpow_inv_const hp0).mul_const c
        simpa using this
      have hev : ∀ᶠ r : ℕ in atTop, b < p ^ ((r : ℝ)⁻¹) * c := (tendsto_order.1 hlim).1 b hbc
      filter_upwards [hev, Filter.eventually_gt_atTop 0] with r hr hr0
      refine lt_of_lt_of_le hr ?_
      have hbase : p * c ^ r ≤ ∫ x, F x ^ r ∂ρ :=
        measureReal_mul_pow_le_integral_pow ρ hF h0 h1 hc0.le r
      have hstep : (p * c ^ r) ^ ((r : ℝ)⁻¹) ≤ (∫ x, F x ^ r ∂ρ) ^ ((r : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hbase (by positivity)
      have hrne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr0.ne'
      refine le_trans (le_of_eq ?_) hstep
      rw [Real.mul_rpow hp0.le (by positivity), ← Real.rpow_natCast c r, ← Real.rpow_mul hc0.le,
        mul_inv_cancel₀ hrne, Real.rpow_one]
  · -- upper half
    intro b hb
    filter_upwards [Filter.eventually_gt_atTop 0] with r hr0
    have hrne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr0.ne'
    have hbase := integral_pow_le_essSup_pow ρ hF h0 h1 r
    have hstep : (∫ x, F x ^ r ∂ρ) ^ ((r : ℝ)⁻¹) ≤ (essSup F ρ ^ r) ^ ((r : ℝ)⁻¹) :=
      Real.rpow_le_rpow (integral_pow_nonneg ρ h0 r) hbase (by positivity)
    refine lt_of_le_of_lt (le_trans hstep (le_of_eq ?_)) hb
    rw [← Real.rpow_natCast (essSup F ρ) r, ← Real.rpow_mul hM0, mul_inv_cancel₀ hrne,
      Real.rpow_one]

/-- **Moment monotonicity.**  Hölder's inequality against the constant one makes the normalized
moments increase with the exponent. -/
theorem integral_pow_le_rpow_integral_pow_succ {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) {r : ℕ} (hr : 0 < r) :
    ∫ x, F x ^ r ∂ρ ≤ (∫ x, F x ^ (r + 1) ∂ρ) ^ ((r : ℝ) / ((r : ℝ) + 1)) := by
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have hr1ne : (r : ℝ) + 1 ≠ 0 := by positivity
  have hp1 : 1 < ((r : ℝ) + 1) / r := by rw [lt_div_iff₀ hr0]; linarith
  have hpq : (((r : ℝ) + 1) / r).HolderConjugate ((r : ℝ) + 1) := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp1, ?_⟩
    rw [inv_div]
    field_simp
  have hmemf : MemLp (fun x => F x ^ r) (ENNReal.ofReal (((r : ℝ) + 1) / r)) ρ := by
    refine MemLp.of_bound (hF.pow_const r).aestronglyMeasurable 1 ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (pow_nonneg (h0 x) r)]
    exact pow_le_one₀ (h0 x) (h1 x)
  have hmemg : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal ((r : ℝ) + 1)) ρ :=
    MemLp.of_bound aestronglyMeasurable_const 1 (by filter_upwards with x; simp)
  have hbase := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ρ) hpq
    (f := fun x => F x ^ r) (g := fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun x => pow_nonneg (h0 x) r)
    (Filter.Eventually.of_forall fun _ => zero_le_one) hmemf hmemg
  simp only [mul_one, Real.one_rpow] at hbase
  rw [show (∫ _x : Ω, (1 : ℝ) ∂ρ) = 1 by simp, Real.one_rpow, mul_one] at hbase
  have hpow : ∀ x, (F x ^ r) ^ (((r : ℝ) + 1) / r) = F x ^ (r + 1) := by
    intro x
    rw [← Real.rpow_natCast (F x) r, ← Real.rpow_mul (h0 x),
      ← Real.rpow_natCast (F x) (r + 1)]
    congr 1
    push_cast
    field_simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hpow)] at hbase
  rw [show (1 : ℝ) / (((r : ℝ) + 1) / r) = (r : ℝ) / ((r : ℝ) + 1) by
    rw [one_div, inv_div]] at hbase
  exact hbase

/-- **Normalized moment monotonicity.**  The exponent-th roots of the moments increase. -/
theorem rpow_inv_integral_pow_monotone {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) {r : ℕ} (hr : 0 < r) :
    (∫ x, F x ^ r ∂ρ) ^ ((r : ℝ)⁻¹) ≤ (∫ x, F x ^ (r + 1) ∂ρ) ^ (((r : ℝ) + 1)⁻¹) := by
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hbase := integral_pow_le_rpow_integral_pow_succ ρ hF h0 h1 hr
  have hnn : 0 ≤ ∫ x, F x ^ (r + 1) ∂ρ := integral_pow_nonneg ρ h0 (r + 1)
  have hstep : (∫ x, F x ^ r ∂ρ) ^ ((r : ℝ)⁻¹) ≤
      ((∫ x, F x ^ (r + 1) ∂ρ) ^ ((r : ℝ) / (r + 1))) ^ ((r : ℝ)⁻¹) :=
    Real.rpow_le_rpow (integral_pow_nonneg ρ h0 r) hbase (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  rw [← Real.rpow_mul hnn]
  congr 1
  field_simp

end PowerMean

end

end GaloisForLFunctions.HTGeometry
