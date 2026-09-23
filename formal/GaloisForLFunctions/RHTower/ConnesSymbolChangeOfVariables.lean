import Mathlib
import GaloisForLFunctions.RHTower.ConnesLocalTraceCore

/-!
# Connes' local trace formula: the change of variables `u = x ξ`

Formalization of the step (29) ⟶ (31) of the proof of Theorem 3 of §V of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

After the Parseval step the cut-off trace is the symbol integral over the square

  `Trace (R_Λ T) = ρ^{-1} ∫_{|x| ≤ Λ, |ξ| ≤ Λ} ĝ(x ξ) dx dξ`,                (29)

and Connes substitutes `u = x ξ`, `dx dξ = du dx/|x|`, so that the `x`-fibre over a frequency `u`
is the window `|u|/Λ ≤ |x| ≤ Λ` of multiplicative mass

  `ρ^{-1} ∫_{|u|/Λ ≤ |x| ≤ Λ} dx/|x| = 2 log' Λ - log|u|`,                    (30)

giving

  `Trace (R_Λ T) = ∫_{|u| ≤ Λ²} ĝ(u) (2 log' Λ - log|u|) du`.                 (31)

Everything here is proved unconditionally at the real place (`ρ = 2`, `log' Λ = log Λ`):

* `connes_scaleWindow_integral` - the window mass (30).
* `connes_inner_substitution` - the inner substitution in `ξ`.
* `connes_fubiniIntegrand_integrable` - the product integrability that licenses Fubini.
* `connes_symbol_changeOfVariables` - the identity (29) = (31).
* `connes_symbolIntegral_tendsto` - chaining with `ConnesLocalTraceCore`, the full analytic
  statement (29) ⟶ (33) of Theorem V.3.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory Set Real Filter Topology intervalIntegral

/-- The `x`-window of Connes' §V (30): the set of scales contributing to a frequency `u`. -/
def connesScaleWindow (Λ u : ℝ) : Set ℝ := {x : ℝ | |u| / Λ ≤ |x| ∧ |x| ≤ Λ}

theorem connesScaleWindow_eq {Λ u : ℝ} (hΛ : 0 < Λ) :
    connesScaleWindow Λ u = Icc (-Λ) (-(|u| / Λ)) ∪ Icc (|u| / Λ) Λ := by
  have hq : 0 ≤ |u| / Λ := by positivity
  ext x
  simp only [connesScaleWindow, mem_setOf_eq, mem_union, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    rcases le_or_gt x 0 with hx | hx
    · left
      rw [abs_of_nonpos hx] at h1 h2
      constructor <;> linarith
    · right
      rw [abs_of_pos hx] at h1 h2
      exact ⟨h1, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have hxneg : x ≤ 0 := le_trans h2 (by linarith)
      rw [abs_of_nonpos hxneg]
      constructor <;> linarith
    · have hxpos : 0 ≤ x := le_trans hq h1
      rw [abs_of_nonneg hxpos]
      exact ⟨h1, h2⟩

/-- **§V (30).**  The `x`-window integral of the multiplicative Haar density. -/
theorem connes_scaleWindow_integral {Λ u : ℝ} (hΛ : 0 < Λ) (hu0 : u ≠ 0)
    (hu : |u| ≤ Λ ^ (2 : ℕ)) :
    (∫ x in connesScaleWindow Λ u, |x|⁻¹) = 2 * (2 * Real.log Λ - Real.log |u|) := by
  have hq0 : (0:ℝ) < |u| / Λ := div_pos (abs_pos.mpr hu0) hΛ
  have hqΛ : |u| / Λ ≤ Λ := by
    rw [div_le_iff₀ hΛ]; nlinarith
  have hdisj : Disjoint (Icc (-Λ) (-(|u| / Λ))) (Icc (|u| / Λ) Λ) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx2⟩ ⟨hx3, -⟩
    linarith
  have hcont : ContinuousOn (fun x : ℝ => |x|⁻¹)
      (Icc (-Λ) (-(|u| / Λ)) ∪ Icc (|u| / Λ) Λ) := by
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    rintro x (⟨-, hx2⟩ | ⟨hx1, -⟩)
    · have : x < 0 := lt_of_le_of_lt hx2 (by linarith)
      exact ne_of_gt (abs_pos.mpr (ne_of_lt this))
    · have : (0:ℝ) < x := lt_of_lt_of_le hq0 hx1
      exact ne_of_gt (abs_pos.mpr (ne_of_gt this))
  have hint1 : IntegrableOn (fun x : ℝ => |x|⁻¹) (Icc (-Λ) (-(|u| / Λ))) :=
    (hcont.mono Set.subset_union_left).integrableOn_compact isCompact_Icc
  have hint2 : IntegrableOn (fun x : ℝ => |x|⁻¹) (Icc (|u| / Λ) Λ) :=
    (hcont.mono Set.subset_union_right).integrableOn_compact isCompact_Icc
  have hpos : (∫ x in Icc (|u| / Λ) Λ, |x|⁻¹) = 2 * Real.log Λ - Real.log |u| := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hqΛ]
    have hcongr : ∀ x ∈ Set.uIcc (|u| / Λ) Λ, |x|⁻¹ = x⁻¹ := by
      intro x hx
      rw [Set.uIcc_of_le hqΛ] at hx
      have hx0 : (0:ℝ) < x := lt_of_lt_of_le hq0 hx.1
      rw [abs_of_pos hx0]
    rw [intervalIntegral.integral_congr hcongr, integral_inv (by
      rw [Set.uIcc_of_le hqΛ]
      simp only [Set.mem_Icc, not_and, not_le]
      intro h
      linarith)]
    rw [div_div_eq_mul_div, Real.log_div (by positivity) (ne_of_gt (abs_pos.mpr hu0))]
    have : Real.log (Λ * Λ) = 2 * Real.log Λ := by
      rw [Real.log_mul (ne_of_gt hΛ) (ne_of_gt hΛ)]; ring
    rw [this]
  have hneg : (∫ x in Icc (-Λ) (-(|u| / Λ)), |x|⁻¹) = 2 * Real.log Λ - Real.log |u| := by
    have hle : (-Λ:ℝ) ≤ -(|u| / Λ) := by linarith
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle]
    have hcongr : ∀ x ∈ Set.uIcc (-Λ) (-(|u| / Λ)), |x|⁻¹ = -x⁻¹ := by
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      have hx0 : x < 0 := lt_of_le_of_lt hx.2 (by linarith)
      rw [abs_of_neg hx0]
      field_simp
    rw [intervalIntegral.integral_congr hcongr]
    have hneg' : (∫ x in (-Λ)..(-(|u| / Λ)), -x⁻¹) = -∫ x in (-Λ)..(-(|u| / Λ)), x⁻¹ :=
      intervalIntegral.integral_neg
    rw [hneg', integral_inv (by
      rw [Set.uIcc_of_le hle]
      simp only [Set.mem_Icc, not_and, not_le]
      intro h
      linarith)]
    have hratio : (-(|u| / Λ)) / (-Λ) = |u| / Λ / Λ := by
      field_simp
    rw [hratio, Real.log_div (ne_of_gt hq0) (ne_of_gt hΛ),
      Real.log_div (ne_of_gt (abs_pos.mpr hu0)) (ne_of_gt hΛ)]
    ring
  rw [connesScaleWindow_eq hΛ, setIntegral_union hdisj measurableSet_Icc hint1 hint2,
    hpos, hneg]
  ring

/-- The two-variable integrand of Connes' §V (29). -/
def connesFubiniSet (Λ : ℝ) : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | |q.1| ≤ Λ ∧ |q.2| ≤ Λ * |q.1|}

theorem measurableSet_connesFubiniSet (Λ : ℝ) : MeasurableSet (connesFubiniSet Λ) := by
  have h1 : MeasurableSet {q : ℝ × ℝ | |q.1| ≤ Λ} :=
    measurableSet_le (measurable_fst.norm) measurable_const
  have h2 : MeasurableSet {q : ℝ × ℝ | |q.2| ≤ Λ * |q.1|} :=
    measurableSet_le (measurable_snd.norm) (measurable_const.mul measurable_fst.norm)
  have : connesFubiniSet Λ = {q : ℝ × ℝ | |q.1| ≤ Λ} ∩ {q : ℝ × ℝ | |q.2| ≤ Λ * |q.1|} := rfl
  rw [this]
  exact h1.inter h2

def connesFubiniIntegrand (G : SchwartzMap ℝ ℂ) (Λ : ℝ) (q : ℝ × ℝ) : ℂ :=
  Set.indicator (connesFubiniSet Λ) (fun q : ℝ × ℝ => ((|q.1|⁻¹ : ℝ) : ℂ) * G q.2) q

theorem connesFubiniIntegrand_slice_snd (G : SchwartzMap ℝ ℂ) {Λ x : ℝ} (hx : |x| ≤ Λ) (u : ℝ) :
    connesFubiniIntegrand G Λ (x, u)
      = Set.indicator {u : ℝ | |u| ≤ Λ * |x|} (fun u : ℝ => ((|x|⁻¹ : ℝ) : ℂ) * G u) u := by
  by_cases hu : |u| ≤ Λ * |x|
  · have h1 : (x, u) ∈ connesFubiniSet Λ := ⟨hx, hu⟩
    have h2 : u ∈ {v : ℝ | |v| ≤ Λ * |x|} := hu
    rw [connesFubiniIntegrand, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
  · have h1 : (x, u) ∉ connesFubiniSet Λ := fun hc => hu hc.2
    have h2 : u ∉ {v : ℝ | |v| ≤ Λ * |x|} := hu
    rw [connesFubiniIntegrand, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

theorem connesFubiniIntegrand_slice_fst (G : SchwartzMap ℝ ℂ) {Λ : ℝ} (hΛ : 0 < Λ) (u x : ℝ) :
    connesFubiniIntegrand G Λ (x, u)
      = Set.indicator (connesScaleWindow Λ u) (fun x : ℝ => ((|x|⁻¹ : ℝ) : ℂ) * G u) x := by
  have hiff : ((x, u) ∈ connesFubiniSet Λ) ↔ (x ∈ connesScaleWindow Λ u) := by
    simp only [connesFubiniSet, connesScaleWindow, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [div_le_iff₀ hΛ]; linarith [h2], h1⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [div_le_iff₀ hΛ] at h1
      linarith
  by_cases hx : (x, u) ∈ connesFubiniSet Λ
  · rw [connesFubiniIntegrand, Set.indicator_of_mem hx,
      Set.indicator_of_mem (hiff.mp hx)]
  · rw [connesFubiniIntegrand, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun hc => hx (hiff.mpr hc))]

theorem connesScaleWindow_eq_empty {Λ u : ℝ} (hΛ : 0 < Λ) (hu : Λ ^ (2 : ℕ) < |u|) :
    connesScaleWindow Λ u = ∅ := by
  ext x
  simp only [connesScaleWindow, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1
  have : Λ < |u| / Λ := by
    rw [lt_div_iff₀ hΛ]; nlinarith
  linarith [h1, this]

theorem measurableSet_connesScaleWindow (Λ u : ℝ) : MeasurableSet (connesScaleWindow Λ u) := by
  have h1 : MeasurableSet {x : ℝ | |u| / Λ ≤ |x|} :=
    measurableSet_le measurable_const measurable_norm
  have h2 : MeasurableSet {x : ℝ | |x| ≤ Λ} :=
    measurableSet_le measurable_norm measurable_const
  have : connesScaleWindow Λ u = {x : ℝ | |u| / Λ ≤ |x|} ∩ {x : ℝ | |x| ≤ Λ} := rfl
  rw [this]
  exact h1.inter h2

/-- The `x`-slice norm integral of the two-variable integrand. -/
theorem connes_fubini_slice_norm (G : SchwartzMap ℝ ℂ) {Λ : ℝ} (hΛ : 0 < Λ) {u : ℝ}
    (hu : u ≠ 0) :
    (∫ x : ℝ, ‖connesFubiniIntegrand G Λ (x, u)‖)
      = ‖G u‖ * Set.indicator {v : ℝ | |v| ≤ Λ ^ (2 : ℕ)}
        (fun v : ℝ => 2 * (2 * Real.log Λ - Real.log |v|)) u := by
  have hslice : ∀ x : ℝ, ‖connesFubiniIntegrand G Λ (x, u)‖
      = Set.indicator (connesScaleWindow Λ u) (fun x : ℝ => ‖G u‖ * |x|⁻¹) x := by
    intro x
    rw [connesFubiniIntegrand_slice_fst G hΛ u x]
    by_cases hx : x ∈ connesScaleWindow Λ u
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_inv, abs_abs]
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero]
  simp only [hslice]
  rw [MeasureTheory.integral_indicator (measurableSet_connesScaleWindow Λ u),
    MeasureTheory.integral_const_mul]
  by_cases hcase : |u| ≤ Λ ^ (2 : ℕ)
  · have hmem : u ∈ {v : ℝ | |v| ≤ Λ ^ (2 : ℕ)} := hcase
    rw [Set.indicator_of_mem hmem, connes_scaleWindow_integral hΛ hu hcase]
  · have hmem : u ∉ {v : ℝ | |v| ≤ Λ ^ (2 : ℕ)} := hcase
    rw [Set.indicator_of_notMem hmem, connesScaleWindow_eq_empty hΛ (not_le.mp hcase)]
    simp

theorem connes_scaleWindow_integrableOn {Λ u : ℝ} (hΛ : 0 < Λ) (hu0 : u ≠ 0) :
    IntegrableOn (fun x : ℝ => |x|⁻¹) (connesScaleWindow Λ u) := by
  by_cases hcase : |u| ≤ Λ ^ (2 : ℕ)
  · have hq0 : (0:ℝ) < |u| / Λ := div_pos (abs_pos.mpr hu0) hΛ
    have hqΛ : |u| / Λ ≤ Λ := by rw [div_le_iff₀ hΛ]; nlinarith
    have hcont : ContinuousOn (fun x : ℝ => |x|⁻¹)
        (Icc (-Λ) (-(|u| / Λ)) ∪ Icc (|u| / Λ) Λ) := by
      refine ContinuousOn.inv₀ (by fun_prop) ?_
      rintro x (⟨-, hx2⟩ | ⟨hx1, -⟩)
      · have : x < 0 := lt_of_le_of_lt hx2 (by linarith)
        exact ne_of_gt (abs_pos.mpr (ne_of_lt this))
      · have : (0:ℝ) < x := lt_of_lt_of_le hq0 hx1
        exact ne_of_gt (abs_pos.mpr (ne_of_gt this))
    rw [connesScaleWindow_eq hΛ]
    exact ((hcont.mono Set.subset_union_left).integrableOn_compact isCompact_Icc).union
      ((hcont.mono Set.subset_union_right).integrableOn_compact isCompact_Icc)
  · rw [connesScaleWindow_eq_empty hΛ (not_le.mp hcase)]
    exact integrableOn_empty

theorem connes_fubiniIntegrand_integrable (G : SchwartzMap ℝ ℂ) {Λ : ℝ} (hΛ : 1 < Λ) :
    Integrable (connesFubiniIntegrand G Λ) (volume.prod volume) := by
  have hΛ0 : (0:ℝ) < Λ := lt_trans one_pos hΛ
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg (le_of_lt hΛ)
  have hmeas : AEStronglyMeasurable (connesFubiniIntegrand G Λ) (volume.prod volume) := by
    refine AEStronglyMeasurable.indicator ?_ (measurableSet_connesFubiniSet Λ)
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
        ((measurable_fst.norm.inv).aestronglyMeasurable))
    · exact (G.continuous.aestronglyMeasurable.comp_measurable measurable_snd)
  have hae0 : ∀ᵐ u : ℝ, u ≠ 0 := by
    have h0 : (volume : Measure ℝ) {(0:ℝ)} = 0 := Real.volume_singleton
    filter_upwards [compl_mem_ae_iff.2 h0] with u hu
    simpa using hu
  rw [integrable_prod_iff' hmeas]
  constructor
  · filter_upwards [hae0] with u hu
    have hslice : (fun x : ℝ => connesFubiniIntegrand G Λ (x, u))
        = Set.indicator (connesScaleWindow Λ u)
          (fun x : ℝ => ((|x|⁻¹ : ℝ) : ℂ) * G u) :=
      funext (connesFubiniIntegrand_slice_fst G hΛ0 u)
    rw [hslice, ← integrableOn_univ,
      integrableOn_indicator_iff (measurableSet_connesScaleWindow Λ u)]
    have hwin := connes_scaleWindow_integrableOn hΛ0 hu
    have : IntegrableOn (fun x : ℝ => ((|x|⁻¹ : ℝ) : ℂ) * G u) (connesScaleWindow Λ u) := by
      have hr : IntegrableOn (fun x : ℝ => ((|x|⁻¹ : ℝ) : ℂ)) (connesScaleWindow Λ u) :=
        hwin.ofReal
      exact hr.mul_const _
    simpa using this
  · have hcongr : (fun u : ℝ => ∫ x : ℝ, ‖connesFubiniIntegrand G Λ (x, u)‖)
        =ᵐ[volume] fun u : ℝ => ‖G u‖ * Set.indicator {v : ℝ | |v| ≤ Λ ^ (2 : ℕ)}
          (fun v : ℝ => 2 * (2 * Real.log Λ - Real.log |v|)) u := by
      filter_upwards [hae0] with u hu
      exact connes_fubini_slice_norm G hΛ0 hu
    refine Integrable.congr ?_ hcongr.symm
    have hb1 : Integrable (fun u : ℝ => (4 * Real.log Λ) * ‖G u‖) :=
      (G.integrable.norm).const_mul _
    have hb2 : Integrable (fun u : ℝ => 2 * (‖G u‖ * abs (Real.log |u|))) := by
      have h := (connes_schwartz_integrable_log G).norm
      have hcong : (fun u : ℝ => ‖G u * ((Real.log |u| : ℝ) : ℂ)‖)
          = fun u : ℝ => ‖G u‖ * abs (Real.log |u|) := by
        funext u
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [hcong] at h
      exact h.const_mul 2
    refine Integrable.mono' (hb1.add hb2) ?_ ?_
    · refine (G.continuous.norm.aestronglyMeasurable).mul ?_
      refine AEStronglyMeasurable.indicator ?_ (measurableSet_le measurable_norm measurable_const)
      exact ((measurable_const.sub (measurable_norm.log)).const_mul 2).aestronglyMeasurable
    · filter_upwards with u
      have hGnn : (0:ℝ) ≤ ‖G u‖ := norm_nonneg _
      by_cases hc : |u| ≤ Λ ^ (2 : ℕ)
      · have hmem : u ∈ {v : ℝ | |v| ≤ Λ ^ (2 : ℕ)} := hc
        rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_mul, abs_of_nonneg hGnn]
        have htri : abs (2 * Real.log Λ - Real.log |u|)
            ≤ abs (2 * Real.log Λ) + abs (Real.log |u|) :=
          abs_sub (2 * Real.log Λ) (Real.log |u|)
        have h2 : abs (2 * Real.log Λ) = 2 * Real.log Λ :=
          abs_of_nonneg (by linarith)
        have hb : abs (2 * (2 * Real.log Λ - Real.log |u|))
            ≤ 4 * Real.log Λ + 2 * abs (Real.log |u|) := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
          rw [h2] at htri
          linarith
        simp only [Pi.add_apply]
        nlinarith [hGnn, hb, abs_nonneg (Real.log |u|)]
      · have hmem : u ∉ {v : ℝ | |v| ≤ Λ ^ (2 : ℕ)} := hc
        rw [Set.indicator_of_notMem hmem, mul_zero, norm_zero]
        simp only [Pi.add_apply]
        positivity

/-- **§V (29), the inner substitution `u = x ξ`.** -/
theorem connes_inner_substitution (G : SchwartzMap ℝ ℂ) {Λ x : ℝ} (hx : x ≠ 0) (hxΛ : |x| ≤ Λ) :
    (∫ u : ℝ, connesFubiniIntegrand G Λ (x, u)) = ∫ ξ in {ξ : ℝ | |ξ| ≤ Λ}, G (x * ξ) := by
  have hxpos : (0:ℝ) < |x| := abs_pos.mpr hx
  set H : ℝ → ℂ := Set.indicator {u : ℝ | |u| ≤ Λ * |x|} (fun u : ℝ => G u) with hH
  have hmemiff : ∀ ξ : ℝ, (x * ξ ∈ {u : ℝ | |u| ≤ Λ * |x|}) ↔ (ξ ∈ {ξ : ℝ | |ξ| ≤ Λ}) := by
    intro ξ
    simp only [Set.mem_setOf_eq, abs_mul]
    constructor
    · intro h
      have h' : |ξ| * |x| ≤ Λ * |x| := by
        calc |ξ| * |x| = |x| * |ξ| := by ring
          _ ≤ Λ * |x| := h
      exact le_of_mul_le_mul_right h' hxpos
    · intro h
      calc |x| * |ξ| ≤ |x| * Λ := mul_le_mul_of_nonneg_left h hxpos.le
        _ = Λ * |x| := by ring
  have hHcomp : ∀ ξ : ℝ, H (x * ξ)
      = Set.indicator {ξ : ℝ | |ξ| ≤ Λ} (fun ξ : ℝ => G (x * ξ)) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ {ξ : ℝ | |ξ| ≤ Λ}
    · rw [hH, Set.indicator_of_mem ((hmemiff ξ).mpr hξ), Set.indicator_of_mem hξ]
    · rw [hH, Set.indicator_of_notMem (fun hc => hξ ((hmemiff ξ).mp hc)),
        Set.indicator_of_notMem hξ]
  have hleft : (∫ u : ℝ, connesFubiniIntegrand G Λ (x, u))
      = ((|x|⁻¹ : ℝ) : ℂ) * ∫ u : ℝ, H u := by
    have hslice : ∀ u : ℝ, connesFubiniIntegrand G Λ (x, u)
        = ((|x|⁻¹ : ℝ) : ℂ) * H u := by
      intro u
      rw [connesFubiniIntegrand_slice_snd G hxΛ u, hH]
      by_cases hu : u ∈ {v : ℝ | |v| ≤ Λ * |x|}
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]
    simp only [hslice]
    rw [MeasureTheory.integral_const_mul]
  have hright : (∫ ξ in {ξ : ℝ | |ξ| ≤ Λ}, G (x * ξ)) = ((|x|⁻¹ : ℝ) : ℂ) * ∫ u : ℝ, H u := by
    have hmeasξ : MeasurableSet {ξ : ℝ | |ξ| ≤ Λ} :=
      measurableSet_le measurable_norm measurable_const
    have hind := MeasureTheory.integral_indicator (μ := (volume : Measure ℝ))
      (f := fun ξ : ℝ => G (x * ξ)) hmeasξ
    rw [← hind]
    have hcongr : (fun ξ : ℝ => Set.indicator {ξ : ℝ | |ξ| ≤ Λ}
        (fun ξ : ℝ => G (x * ξ)) ξ) = fun ξ : ℝ => H (x * ξ) := by
      funext ξ; exact (hHcomp ξ).symm
    rw [hcongr, Measure.integral_comp_mul_left H x, Complex.real_smul, abs_inv]
  rw [hleft, hright]

/-- **§V (29) ⟶ (31).**  The change of variables `u = x ξ` turns the cut-off symbol integral over
the square `|x| ≤ Λ`, `|ξ| ≤ Λ` into the frequency integral against the logarithmic weight
`2 log' Λ - log|u|` over `|u| ≤ Λ²`. -/
theorem connes_symbol_changeOfVariables (G : SchwartzMap ℝ ℂ) {Λ : ℝ} (hΛ : 1 < Λ) :
    (2:ℂ)⁻¹ * (∫ x in {x : ℝ | |x| ≤ Λ}, ∫ ξ in {ξ : ℝ | |ξ| ≤ Λ}, G (x * ξ))
      = ∫ u in {u : ℝ | |u| ≤ Λ ^ (2 : ℕ)}, G u * (((2 * Real.log Λ - Real.log |u|) : ℝ) : ℂ) := by
  have hΛ0 : (0:ℝ) < Λ := lt_trans one_pos hΛ
  have hae0 : ∀ᵐ u : ℝ, u ≠ 0 := by
    have h0 : (volume : Measure ℝ) {(0:ℝ)} = 0 := Real.volume_singleton
    filter_upwards [compl_mem_ae_iff.2 h0] with u hu
    simpa using hu
  have hmeasX : MeasurableSet {x : ℝ | |x| ≤ Λ} :=
    measurableSet_le measurable_norm measurable_const
  have hmeasU : MeasurableSet {u : ℝ | |u| ≤ Λ ^ (2 : ℕ)} :=
    measurableSet_le measurable_norm measurable_const
  -- step A: the iterated integral in `x` first
  have hstepA : (∫ x : ℝ, ∫ u : ℝ, connesFubiniIntegrand G Λ (x, u))
      = ∫ x in {x : ℝ | |x| ≤ Λ}, ∫ ξ in {ξ : ℝ | |ξ| ≤ Λ}, G (x * ξ) := by
    rw [← MeasureTheory.integral_indicator hmeasX]
    refine integral_congr_ae ?_
    filter_upwards [hae0] with x hx
    by_cases hxΛ : x ∈ {x : ℝ | |x| ≤ Λ}
    · rw [Set.indicator_of_mem hxΛ]
      exact connes_inner_substitution G hx hxΛ
    · rw [Set.indicator_of_notMem hxΛ]
      have hzero : ∀ u : ℝ, connesFubiniIntegrand G Λ (x, u) = 0 := by
        intro u
        rw [connesFubiniIntegrand, Set.indicator_of_notMem (fun hc => hxΛ hc.1)]
      simp only [hzero, integral_zero]
  -- step B: Fubini
  have hstepB : (∫ x : ℝ, ∫ u : ℝ, connesFubiniIntegrand G Λ (x, u))
      = ∫ u : ℝ, ∫ x : ℝ, connesFubiniIntegrand G Λ (x, u) := by
    refine MeasureTheory.integral_integral_swap ?_
    exact connes_fubiniIntegrand_integrable G hΛ
  -- step C: the inner `x`-integral is the logarithmic weight
  have hstepC : (∫ u : ℝ, ∫ x : ℝ, connesFubiniIntegrand G Λ (x, u))
      = 2 * ∫ u in {u : ℝ | |u| ≤ Λ ^ (2 : ℕ)},
          G u * (((2 * Real.log Λ - Real.log |u|) : ℝ) : ℂ) := by
    rw [← MeasureTheory.integral_indicator hmeasU, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae0] with u hu
    have hslice : ∀ x : ℝ, connesFubiniIntegrand G Λ (x, u)
        = Set.indicator (connesScaleWindow Λ u) (fun x : ℝ => ((|x|⁻¹ : ℝ) : ℂ)) x * G u := by
      intro x
      rw [connesFubiniIntegrand_slice_fst G hΛ0 u x]
      by_cases hx : x ∈ connesScaleWindow Λ u
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
    simp only [hslice]
    rw [MeasureTheory.integral_mul_const,
      MeasureTheory.integral_indicator (measurableSet_connesScaleWindow Λ u)]
    by_cases hcase : |u| ≤ Λ ^ (2 : ℕ)
    · have hmem : u ∈ {v : ℝ | |v| ≤ Λ ^ (2 : ℕ)} := hcase
      rw [Set.indicator_of_mem hmem]
      have hwin : IntegrableOn (fun x : ℝ => |x|⁻¹) (connesScaleWindow Λ u) :=
        connes_scaleWindow_integrableOn hΛ0 hu
      have hcast : (∫ x in connesScaleWindow Λ u, ((|x|⁻¹ : ℝ) : ℂ))
          = (((∫ x in connesScaleWindow Λ u, |x|⁻¹ : ℝ)) : ℂ) :=
        integral_complex_ofReal (μ := volume.restrict (connesScaleWindow Λ u))
          (f := fun x : ℝ => |x|⁻¹)
      rw [hcast, connes_scaleWindow_integral hΛ0 hu hcase]
      push_cast
      ring
    · have hmem : u ∉ {v : ℝ | |v| ≤ Λ ^ (2 : ℕ)} := hcase
      rw [Set.indicator_of_notMem hmem, connesScaleWindow_eq_empty hΛ0 (not_le.mp hcase)]
      simp
  rw [← hstepA, hstepB, hstepC]
  rw [← mul_assoc]
  norm_num

/-- **Theorem V.3, the full analytic chain (29) ⟶ (33).**  For a Schwartz symbol `ĝ` the cut-off
double integral over the square `|x| ≤ Λ`, `|ξ| ≤ Λ` — which is `Trace (R_Λ U(h))` by the Parseval
step (23)(24) — converges to `2 g(0) log' Λ - ∫ ĝ(u) log|u| du`, the right-hand side of Connes'
local trace formula before the Fourier identification of `-log|u|`. -/
theorem connes_symbolIntegral_tendsto (G : SchwartzMap ℝ ℂ) :
    Tendsto (fun Λ : ℝ =>
      (2:ℂ)⁻¹ * (∫ x in {x : ℝ | |x| ≤ Λ}, ∫ ξ in {ξ : ℝ | |ξ| ≤ Λ}, G (x * ξ))
        - (((2 * Real.log Λ : ℝ) : ℂ) * (∫ u : ℝ, G u)
            - ∫ u : ℝ, G u * ((Real.log |u| : ℝ) : ℂ)))
      atTop (𝓝 0) := by
  refine (connes_traceCore_tendsto G).congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with Λ hΛ
  rw [connes_symbol_changeOfVariables G hΛ]

end

end GaloisForLFunctions.RHTower





