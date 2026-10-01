import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Wiener's lemma for characteristic functions

For a finite measure `ρ` on `ℝ`, the Cesàro mean of its characteristic function recovers the mass
at the origin:

`(1/2Y) ∫_{−Y}^{Y} charFun ρ y dy → ρ({0})`  (`tendsto_mean_charFun`).

Applied to the difference measure of `ν ⊗ ν` this gives **Wiener's lemma**

`(1/2Y) ∫_{−Y}^{Y} |charFun ν y|² dy → (ν ⊗ ν)(diagonal) = Σ_a ν({a})²`
(`tendsto_mean_normSq_charFun`).

So the characteristic function of `ν` decays in mean square iff `ν` has no atoms.

**Proof.**  By Fubini, the Cesàro mean of `charFun ρ` is `∫ m_Y(r) dρ(r)`, where
`m_Y(r) = (1/2Y)∫_{−Y}^{Y} e^{iyr} dy`.  We have `|m_Y| ≤ 1`, `m_Y(0) = 1`, and
`|m_Y(r)| ≤ 1/(Y|r|)` for `r ≠ 0`.  Dominated convergence finishes.  For Wiener's lemma,
`|charFun ν|² = charFun` of the image of `ν ⊗ ν` under `(r, s) ↦ r − s`.
-/

open MeasureTheory Filter Topology Complex Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The Cesàro mean of the plane wave `y ↦ e^{iyr}` over `[−Y, Y]`. -/
def planeWaveMean (Y r : ℝ) : ℂ := (1 / (2 * Y) : ℂ) * ∫ y in (-Y)..Y, cexp (y * r * I)

theorem norm_planeWaveMean_le {Y : ℝ} (hY : 0 < Y) (r : ℝ) : ‖planeWaveMean Y r‖ ≤ 1 := by
  unfold planeWaveMean
  rw [norm_mul]
  have h1 : ‖(1 / (2 * Y) : ℂ)‖ = 1 / (2 * Y) := by
    rw [show (1 / (2 * Y) : ℂ) = ((1 / (2 * Y) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h2 : ‖∫ y in (-Y)..Y, cexp (y * r * I)‖ ≤ 2 * Y := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (a := -Y) (b := Y)
      (f := fun y : ℝ => cexp (y * r * I)) fun y _ => by
        rw [show (y : ℂ) * r * I = ((y * r : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
    rw [show Y - -Y = 2 * Y by ring, abs_of_pos (by linarith : (0 : ℝ) < 2 * Y)] at this
    linarith
  rw [h1]
  calc 1 / (2 * Y) * ‖∫ y in (-Y)..Y, cexp (y * r * I)‖ ≤ 1 / (2 * Y) * (2 * Y) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 := by field_simp

theorem planeWaveMean_zero {Y : ℝ} (hY : 0 < Y) : planeWaveMean Y 0 = 1 := by
  unfold planeWaveMean
  rw [show (fun y : ℝ => cexp (↑y * ↑(0 : ℝ) * I)) = fun _ => (1 : ℂ) by funext y; simp,
    intervalIntegral.integral_const, Complex.real_smul]
  have hY0 : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  push_cast
  field_simp
  ring

theorem norm_planeWaveMean_le_inv {Y r : ℝ} (hY : 0 < Y) (hr : r ≠ 0) :
    ‖planeWaveMean Y r‖ ≤ 1 / (Y * |r|) := by
  unfold planeWaveMean
  have hc : (r : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hr) I_ne_zero
  have hint : ∫ y in (-Y)..Y, cexp (y * r * I) =
      (cexp ((r : ℂ) * I * Y) - cexp ((r : ℂ) * I * (-Y : ℝ))) / ((r : ℂ) * I) := by
    rw [← integral_exp_mul_complex hc]
    congr 1
    funext y
    ring_nf
  have hnum : ‖cexp ((r : ℂ) * I * Y) - cexp ((r : ℂ) * I * (-Y : ℝ))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [show (r : ℂ) * I * Y = ((r * Y : ℝ) : ℂ) * I by push_cast; ring,
      show (r : ℂ) * I * (-Y : ℝ) = ((r * -Y : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hden : ‖(r : ℂ) * I‖ = |r| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖(1 / (2 * Y) : ℂ)‖ = 1 / (2 * Y) := by
    rw [show (1 / (2 * Y) : ℂ) = ((1 / (2 * Y) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hint, norm_mul, h1, norm_div, hden]
  have hr0 : 0 < |r| := abs_pos.mpr hr
  calc 1 / (2 * Y) * (‖cexp ((r : ℂ) * I * Y) - cexp ((r : ℂ) * I * (-Y : ℝ))‖ / |r|)
      ≤ 1 / (2 * Y) * (2 / |r|) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hr0.le) (by positivity)
    _ = 1 / (Y * |r|) := by field_simp

theorem tendsto_planeWaveMean (r : ℝ) :
    Tendsto (fun Y => planeWaveMean Y r) atTop (𝓝 (if r = 0 then 1 else 0)) := by
  split_ifs with hr
  · subst hr
    exact tendsto_const_nhds.congr' ((eventually_gt_atTop 0).mono fun Y hY =>
      (planeWaveMean_zero hY).symm)
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have hr0 : 0 < |r| := abs_pos.mpr hr
    have hlim : Tendsto (fun Y : ℝ => 1 / (Y * |r|)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.atTop_mul_const hr0)
    refine squeeze_zero' (Eventually.of_forall fun Y => norm_nonneg _)
      ((eventually_gt_atTop 0).mono fun Y hY => norm_planeWaveMean_le_inv hY hr) hlim

theorem mean_charFun_eq {ρ : Measure ℝ} [IsFiniteMeasure ρ] {Y : ℝ} (hY : 0 < Y) :
    (1 / (2 * Y) : ℂ) * ∫ y in (-Y)..Y, charFun ρ y = ∫ r, planeWaveMean Y r ∂ρ := by
  simp_rw [charFun_apply_real]
  unfold planeWaveMean
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hswap := integral_integral_swap (μ := volume.restrict (Ioc (-Y) Y)) (ν := ρ)
    (f := fun y r => cexp (↑y * ↑r * I)) ?_
  · rw [hswap]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    rw [intervalIntegral.integral_of_le (by linarith)]
  · refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (Eventually.of_forall fun p => ?_)
    · exact (by fun_prop : Continuous fun p : ℝ × ℝ => cexp (↑p.1 * ↑p.2 * I)).aestronglyMeasurable
    · show ‖cexp (↑p.1 * ↑p.2 * I)‖ ≤ 1
      rw [show (p.1 : ℂ) * p.2 * I = ((p.1 * p.2 : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]

/-- **Cesàro mean of a characteristic function.** -/
theorem tendsto_mean_charFun (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
    Tendsto (fun Y : ℝ => (1 / (2 * Y) : ℂ) * ∫ y in (-Y)..Y, charFun ρ y) atTop
      (𝓝 (ρ.real {0} : ℂ)) := by
  have hlim : Tendsto (fun Y : ℝ => ∫ r, planeWaveMean Y r ∂ρ) atTop
      (𝓝 (∫ r, (if r = 0 then (1 : ℂ) else 0) ∂ρ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const 1) (Eventually.of_forall fun r => tendsto_planeWaveMean r)
    · refine Eventually.of_forall fun Y => ?_
      unfold planeWaveMean
      exact ((by fun_prop : Continuous fun r : ℝ =>
        (1 / (2 * Y) : ℂ) * ∫ y in (-Y)..Y, cexp (y * r * I))).aestronglyMeasurable
    · exact (eventually_gt_atTop 0).mono fun Y hY => Eventually.of_forall fun r =>
        norm_planeWaveMean_le hY r
  have hval : (∫ r, (if r = 0 then (1 : ℂ) else 0) ∂ρ) = (ρ.real {0} : ℂ) := by
    have e : (fun r : ℝ => if r = 0 then (1 : ℂ) else 0) =
        fun r => ((({0} : Set ℝ).indicator (1 : ℝ → ℝ) r : ℝ) : ℂ) := by
      funext r
      by_cases h : r = 0 <;> simp [h, Set.indicator]
    rw [e, integral_complex_ofReal, integral_indicator_one (measurableSet_singleton 0)]
  rw [hval] at hlim
  exact hlim.congr' ((eventually_gt_atTop 0).mono fun Y hY => (mean_charFun_eq hY).symm)

/-- The difference measure `(r, s) ↦ r − s` of `ν ⊗ ν`. -/
def diffMeasure (ν : Measure ℝ) : Measure ℝ := (ν.prod ν).map fun p => p.1 - p.2

instance (ν : Measure ℝ) [IsFiniteMeasure ν] : IsFiniteMeasure (diffMeasure ν) := by
  unfold diffMeasure; infer_instance

theorem charFun_diffMeasure (ν : Measure ℝ) [IsFiniteMeasure ν] (y : ℝ) :
    charFun (diffMeasure ν) y = ((‖charFun ν y‖ ^ 2 : ℝ) : ℂ) := by
  have hm : Measurable fun p : ℝ × ℝ => p.1 - p.2 := by fun_prop
  rw [charFun_apply_real, diffMeasure, integral_map hm.aemeasurable
    (by fun_prop : Continuous fun x : ℝ => cexp (↑y * ↑x * I)).aestronglyMeasurable]
  have hsplit : ∀ p : ℝ × ℝ, cexp (↑y * ↑(p.1 - p.2) * I) =
      cexp (↑y * ↑p.1 * I) * cexp (↑(-y) * ↑p.2 * I) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hsplit]
  rw [integral_prod_mul (fun x : ℝ => cexp (↑y * ↑x * I)) (fun x : ℝ => cexp (↑(-y) * ↑x * I)),
    ← charFun_apply_real, ← charFun_apply_real, charFun_neg, Complex.mul_conj, Complex.sq_norm]

theorem diffMeasure_real_zero (ν : Measure ℝ) [IsFiniteMeasure ν] :
    (diffMeasure ν).real {0} = (ν.prod ν).real {p : ℝ × ℝ | p.1 = p.2} := by
  have hm : Measurable fun p : ℝ × ℝ => p.1 - p.2 := by fun_prop
  unfold diffMeasure
  rw [measureReal_def, measureReal_def, Measure.map_apply hm (measurableSet_singleton 0)]
  congr 2
  ext p
  simp [sub_eq_zero]

/-- **Wiener's lemma.**  The mean square of the characteristic function of a finite measure on
`ℝ` tends to the mass of the diagonal of `ν ⊗ ν`, i.e. to `Σ_a ν({a})²`. -/
theorem tendsto_mean_normSq_charFun (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Tendsto (fun Y : ℝ => (1 / (2 * Y)) * ∫ y in (-Y)..Y, ‖charFun ν y‖ ^ 2) atTop
      (𝓝 ((ν.prod ν).real {p : ℝ × ℝ | p.1 = p.2})) := by
  have h := tendsto_mean_charFun (diffMeasure ν)
  rw [diffMeasure_real_zero] at h
  have hre := (Complex.continuous_re.tendsto _).comp h
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  refine hre.congr' ((eventually_gt_atTop 0).mono fun Y hY => ?_)
  simp_rw [charFun_diffMeasure]
  rw [intervalIntegral.integral_ofReal]
  rw [show (1 / (2 * (Y : ℂ))) = ((1 / (2 * Y) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-! ## One-sided means at a frequency -/

/-- The one-sided Cesàro mean of the plane wave `y ↦ e^{iyu}` over `[0, Y]`. -/
def oneSidedWaveMean (Y u : ℝ) : ℂ := (1 / Y : ℂ) * ∫ y in (0 : ℝ)..Y, cexp (y * u * I)

theorem norm_oneSidedWaveMean_le {Y : ℝ} (hY : 0 < Y) (u : ℝ) : ‖oneSidedWaveMean Y u‖ ≤ 1 := by
  unfold oneSidedWaveMean
  rw [norm_mul]
  have h1 : ‖(1 / Y : ℂ)‖ = 1 / Y := by
    rw [show (1 / Y : ℂ) = ((1 / Y : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h2 : ‖∫ y in (0 : ℝ)..Y, cexp (y * u * I)‖ ≤ Y := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (a := 0) (b := Y)
      (f := fun y : ℝ => cexp (y * u * I)) fun y _ => by
        rw [show (y : ℂ) * u * I = ((y * u : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
    rw [sub_zero, abs_of_pos hY, one_mul] at this
    exact this
  rw [h1]
  calc 1 / Y * ‖∫ y in (0 : ℝ)..Y, cexp (y * u * I)‖ ≤ 1 / Y * Y :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 := by field_simp

theorem oneSidedWaveMean_zero {Y : ℝ} (hY : 0 < Y) : oneSidedWaveMean Y 0 = 1 := by
  unfold oneSidedWaveMean
  rw [show (fun y : ℝ => cexp (↑y * ↑(0 : ℝ) * I)) = fun _ => (1 : ℂ) by funext y; simp,
    intervalIntegral.integral_const, Complex.real_smul]
  have hY0 : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  push_cast
  rw [sub_zero]
  field_simp

theorem norm_oneSidedWaveMean_le_inv {Y u : ℝ} (hY : 0 < Y) (hu : u ≠ 0) :
    ‖oneSidedWaveMean Y u‖ ≤ 2 / (Y * |u|) := by
  unfold oneSidedWaveMean
  have hc : (u : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hu) I_ne_zero
  have hint : ∫ y in (0 : ℝ)..Y, cexp (y * u * I) =
      (cexp ((u : ℂ) * I * Y) - cexp ((u : ℂ) * I * (0 : ℝ))) / ((u : ℂ) * I) := by
    rw [← integral_exp_mul_complex hc]
    congr 1
    funext y
    ring_nf
  have hnum : ‖cexp ((u : ℂ) * I * Y) - cexp ((u : ℂ) * I * (0 : ℝ))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [show (u : ℂ) * I * Y = ((u * Y : ℝ) : ℂ) * I by push_cast; ring,
      show (u : ℂ) * I * (0 : ℝ) = ((u * 0 : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hden : ‖(u : ℂ) * I‖ = |u| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖(1 / Y : ℂ)‖ = 1 / Y := by
    rw [show (1 / Y : ℂ) = ((1 / Y : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hint, norm_mul, h1, norm_div, hden]
  have hu0 : 0 < |u| := abs_pos.mpr hu
  calc 1 / Y * (‖cexp ((u : ℂ) * I * Y) - cexp ((u : ℂ) * I * (0 : ℝ))‖ / |u|)
      ≤ 1 / Y * (2 / |u|) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hu0.le) (by positivity)
    _ = 2 / (Y * |u|) := by field_simp

theorem tendsto_oneSidedWaveMean (u : ℝ) :
    Tendsto (fun Y => oneSidedWaveMean Y u) atTop (𝓝 (if u = 0 then 1 else 0)) := by
  split_ifs with hu
  · subst hu
    exact tendsto_const_nhds.congr' ((eventually_gt_atTop 0).mono fun Y hY =>
      (oneSidedWaveMean_zero hY).symm)
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have hu0 : 0 < |u| := abs_pos.mpr hu
    have hlim : Tendsto (fun Y : ℝ => 2 / (Y * |u|)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.atTop_mul_const hu0)
    exact squeeze_zero' (Eventually.of_forall fun Y => norm_nonneg _)
      ((eventually_gt_atTop 0).mono fun Y hY => norm_oneSidedWaveMean_le_inv hY hu) hlim

/-- **One-sided Cesàro mean at frequency `a`.**  For a finite measure `ρ` on `ℝ`,
`(1/Y) ∫_0^Y charFun ρ (y) e^{−iay} dy → ρ({a})`. -/
theorem tendsto_oneSided_mean_charFun_mul (ρ : Measure ℝ) [IsFiniteMeasure ρ] (a : ℝ) :
    Tendsto (fun Y : ℝ => (1 / Y : ℂ) * ∫ y in (0 : ℝ)..Y, charFun ρ y * cexp (-(y * a * I)))
      atTop (𝓝 (ρ.real {a} : ℂ)) := by
  have hswap : ∀ Y : ℝ, 0 < Y →
      (1 / Y : ℂ) * ∫ y in (0 : ℝ)..Y, charFun ρ y * cexp (-(y * a * I)) =
        ∫ r, oneSidedWaveMean Y (r - a) ∂ρ := by
    intro Y hY
    unfold oneSidedWaveMean
    rw [MeasureTheory.integral_const_mul]
    congr 1
    simp_rw [charFun_apply_real]
    rw [intervalIntegral.integral_of_le hY.le]
    have hmul : ∀ y : ℝ, (∫ x, cexp (↑y * ↑x * I) ∂ρ) * cexp (-(↑y * ↑a * I)) =
        ∫ x, cexp (↑y * ↑(x - a) * I) ∂ρ := by
      intro y
      rw [← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [hmul]
    rw [integral_integral_swap]
    · refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only
      rw [intervalIntegral.integral_of_le hY.le]
    · refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (Eventually.of_forall fun p => ?_)
      · exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
          cexp (↑p.1 * ↑(p.2 - a) * I)).aestronglyMeasurable
      · show ‖cexp (↑p.1 * ↑(p.2 - a) * I)‖ ≤ 1
        rw [show (p.1 : ℂ) * ↑(p.2 - a) * I = ((p.1 * (p.2 - a) : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
  have hlim : Tendsto (fun Y : ℝ => ∫ r, oneSidedWaveMean Y (r - a) ∂ρ) atTop
      (𝓝 (∫ r, (if r - a = 0 then (1 : ℂ) else 0) ∂ρ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const 1) (Eventually.of_forall fun r => tendsto_oneSidedWaveMean (r - a))
    · refine Eventually.of_forall fun Y => ?_
      unfold oneSidedWaveMean
      exact ((by fun_prop : Continuous fun r : ℝ =>
        (1 / Y : ℂ) * ∫ y in (0 : ℝ)..Y, cexp (y * (r - a) * I))).aestronglyMeasurable.congr
        (Eventually.of_forall fun r => by simp)
    · exact (eventually_gt_atTop 0).mono fun Y hY => Eventually.of_forall fun r =>
        norm_oneSidedWaveMean_le hY _
  have hval : (∫ r, (if r - a = 0 then (1 : ℂ) else 0) ∂ρ) = (ρ.real {a} : ℂ) := by
    have e : (fun r : ℝ => if r - a = 0 then (1 : ℂ) else 0) =
        fun r => ((({a} : Set ℝ).indicator (1 : ℝ → ℝ) r : ℝ) : ℂ) := by
      funext r
      by_cases h : r = a <;> simp [h, Set.indicator, sub_eq_zero]
    rw [e, integral_complex_ofReal, integral_indicator_one (measurableSet_singleton a)]
  rw [hval] at hlim
  exact hlim.congr' ((eventually_gt_atTop 0).mono fun Y hY => (hswap Y hY).symm)

end GaloisForLFunctions.HTGeometry
